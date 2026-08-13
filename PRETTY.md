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
`addWireInput`, ordered `actFor` fold, proof-carrying `EndpointAct` escape
wrapper, and discoverable reset/realization library aliases—are in scope only
as definitional or metadata wrappers over existing public values, `Design`
fields, `Act.seq`, and existing endpoint analysis; they may not introduce a new
transition or emission behavior.

The purpose is not to accept or imitate Verilog. It is to make cycle semantics
hard to misread. Hardware nouns and
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

Here `rule` means a named action run on every cycle in visible rule order. It
does not mean a Bluespec scheduled/atomic rule: all reads see start-of-cycle
state, every rule runs, and the last executed write to a target wins.

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
3. A Loom `rule` is a named action executed on every island cycle in visible
   source order. It is not a Bluespec-style atomic rule, has no scheduler, and
   does not compete with neighboring rules for implicit resources. All reads
   observe pre-cycle state and the last executed write wins. There are no
   sensitivity lists. Keep the established core noun for v1 and state this
   divergence beside the first example so `rule` cannot silently imply
   scheduling or atomicity.
4. Numeric literals are unsized and acquire their width from the expected
   `Expr w` type. They are range-checked before `BitVec.ofNat`: a source `n`
   is accepted only when `n < 2 ^ w`. Loom does not add a second width
   declaration with `8'd255`, and it never silently turns `300` into `44` in
   an 8-bit position.
5. Ordering comparisons expose signedness: `<u`/`<s` in an ASCII surface, or
   `<ᵤ`/`<ₛ` in a Unicode surface. There is no unmarked `<` and no expression
   `<=` in v1. Less-or-equal arrives only after `Expr` has distinct unsigned
   and signed constructors and semantics.
6. There are no multi-bit `&&`, `||`, or `!` operators because the core has no
   Verilog truthiness rule. Bitwise operators mirror `Expr.and`, `Expr.or`,
   `Expr.xor`, and `Expr.not`; they may be used on `Expr 1` conditions.
7. Part selects are static because `Expr.slice` takes constant `lo` and
   `width`. Dynamic part and single-bit selects are rejected at their source
   span because the core has no dynamic-select constructor. The diagnostic
   suggests the explicit shift-and-static-select idiom, for example
   `(word >> index)[0]`, and reminds the author that the current shift count
   must have the same width as `word`.
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

The precedence table is part of the public grammar, not merely parser-test
knowledge. From tightest to loosest, v1 uses:

| Level | Forms | Associativity and typing |
| --- | --- | --- |
| postfix | `.field`, `[bit]`, `[hi:lo]`, memory/index forms | tightest, left-chaining; selects are static in v1, so `~x[3]` means `~(x[3])` |
| prefix/extension | `~x`, `zext x to w`, `sext x to w` | unary; a compound extension operand is parenthesized; v1 has no unary minus |
| multiplicative | `*`, `/`, `%` | left; operands and result have one width |
| additive | `+`, `-` | left; operands and result have one width |
| shift | `<<`, `>>` | left; both operands and the result have the left operand's width |
| concatenation | `++` | right; result width is the sum of operand widths |
| bitwise AND | `&` | left; equal-width operands |
| bitwise XOR | `^` | left; equal-width operands |
| bitwise OR | `|` | left; equal-width operands |
| comparison | `==`, `<u`, `<s` | non-associative; equal-width operands, 1-bit result |
| mux | `if c then t else f` | lowest; 1-bit condition and equal-width branches |

Multiplication and addition follow the universal arithmetic convention and
bind more tightly than comparison, so `a + b == c` is legal and means
`(a + b) == c`. The remaining plausible hardware footguns are deliberately
stricter than the row order. Comparison/bitwise, shift/arithmetic, and
concatenation/any other infix boundary require explicit parentheses in either
direction:

```text
a & b == c       -- error: parenthesize either `(a & b)` or `(b == c)`
a == b | c       -- error: comparison/bitwise mixture needs parentheses
a + b << 2       -- error: shift/arithmetic mixture needs parentheses
a << b + 1       -- error: shift/arithmetic mixture needs parentheses
high ++ low + 1  -- error: concatenation boundary needs parentheses
(high ++ low) + 1        -- legal when the resulting widths agree
high ++ (low + 1)        -- legal; `++` remains right-associative
```

Thus both `wakeEn & (tstate[i] == FUTEX)` and `(flags & MASK) == READY` say
exactly what they mean, while the C/Verilog footguns are not assigned one of
two plausible readings. Comparison operators are syntactically
non-associative: `a <u b <u c`, `a == b == c`, and mixed comparison chains are
rejected at the second operator with “comparison chaining is not supported;
combine parenthesized 1-bit comparisons explicitly.” This is a parser rule,
not a width-error accident: a width-one chain must not acquire an absurd but
well-typed meaning. Parentheses are likewise required around a width-changing
extension when it participates in another infix expression.

The core shift constructors require `Expr w` on both sides. Accordingly the
RHS is an unsigned `w`-bit shift count interpreted with `BitVec.toNat`; the
result remains `w` bits, and a count at least `w` produces zero, matching the
current `BitVec` semantics and Verilog's result for a fixed-width operand.
There is no signed shift amount and `>>` is logical, not arithmetic. `>>s` is
explicitly omitted in v1 because the core has no arithmetic-right-shift
constructor. Code needing it uses a named library helper through `$(term)`.
That helper is an explicit core composition: for counts below `w`, sign-extend
to a wider width, zero-extend the count to that same width, logically shift,
and slice back; for larger counts, mux between all-ones and zero from the sign
bit. It must not rely on `>>` to infer signedness, and its overshift behavior
must be tested separately from logical shift.

The equal-width core operand is not exposed as ceremony for static shifts.
`x << 3`, `x >> 0x10`, and `x << SHIFT_AMT` accept a reducible `Nat` literal,
ordinary local, design-local `const` value, or active `@[hw_const]` directly in
shift position; lowering re-lifts that compile-time value to the required
`w`-bit operand after the ordinary range check. A
genuinely dynamic amount remains an `Expr w`, making the potential barrel
shifter visible in its type and cost diagnostics. When a dynamic selector
`x[i]` is rejected and `i` already has width `w`, its diagnostic shows the
literal rewrite `(x >> i)[0]`.

A bare identifier is elaborated using the expected `Expr w` type. It may be a
`Reg w` or `Input w` handle (read through its coercion), an existing `Expr w`
helper, a hygienic local `Nat`, or a global `Nat` deliberately registered with
`@[hw_const]`. A registered constant such as `S_F0` is lifted to `Expr.lit` at
the expected width, which lets state-machine code say `st == S_F0` without an
annotation or escape while keeping the global candidate set intentional:

```lean
@[hw_const FsmStates] def S_F0 : Nat := 0

open scoped FsmStates
```

The attribute validates at the declaration that its target has type `Nat`;
v1 does not register arbitrary types or `BitVec`s. It is a scoped environment
extension, not a typeclass search. A constant declared in the current scope is
eligible there; an imported constant becomes eligible only after its hardware-
constant scope is opened. Merely importing a library cannot add short-name
candidates. An unrelated reachable `Nat` is never considered merely because
it has the right host type. Ordinary local parameters are eligible because
their lexical occurrence is already deliberate; arbitrary Lean computation
still uses `$(term)`.

Resolution has a fixed shadowing rule. Inside a `hardware` command, a unique
design-local declaration (signal, local constant, or state member) wins over
every external candidate with the same short name; collisions between local
declarations are rejected when the command is built. Otherwise the elaborator
considers hygienic locals, ordinary `Expr w` declarations found by Lean name
resolution, and only `@[hw_const]` global `Nat`s from active scopes; exactly
one viable candidate is accepted, while two or more are an ambiguity error at
the identifier. Fully qualified names and `$(term)` remain
available to select an ordinary Lean declaration explicitly. The command may
emit an informational note when a design-local declaration shadows a viable
registered constant, but it must never silently choose between two non-signal
candidates. Adding an unmarked `Nat` elsewhere cannot change elaboration.
Outside a command wrapper there is no design-local table, so the same
unique-candidate rule applies without the signal-priority step.

The expected width `w` must reduce to a concrete `Nat` before automatic value
lifting. A `hardware` declaration already has this property because Loom must
construct its indexed handle. A standalone quotation inside a width-polymorphic
Lean function therefore cannot use an unsized literal until its width is
specialized; it receives a direct diagnostic and may instead use an explicit
typed `$(term)`. Every numeric token, lifted local, and `@[hw_const]` value is
then weak-head-
normalized at its source occurrence, must reduce to a concrete nonnegative
`Nat`, and must pass `n < 2 ^ w`. Failure to reduce is an error—“hardware
constant must reduce to a numeral for range checking”—rather than a reason to
skip checking. Overflow reports the value, expected width, and range before
`BitVec.ofNat` can truncate it. Negative literal syntax is absent in v1;
`-1` in a hardware expression or reset position receives a targeted message
suggesting the explicit `2^w - 1`/all-ones mask idiom. A deliberately modular
value must be written visibly as an `Expr`/`BitVec` Lean term through
`$(term)`.

Source numerals accept decimal, `0x` hexadecimal, and `0b` binary spelling,
with `_` separators in every radix. Radix and separators never change the
value or the same range check. Source-aware inspection metadata preserves the
author's spelling where possible. When no source spelling survives, canonical
delaboration prints decimal below 8 bits and hexadecimal padded to
`ceil(width / 4)` digits at 8 bits or wider; it never changes the typed width
or silently discards leading zeroes that communicate that width.

The initial `hwstmt` forms are:

```lean
r <- expr
packedReg.field <- expr
mem[port n, addr] <- expr
let ident := expr
let ident : type := expr
if cond then branch else branch
if cond then branch else if cond then branch else branch
if cond then branch
{ statement* }
case expr of
| constant => branch
| default => branch
for ident in $(term) generate branch
send expr to channel
send expr to channel then branch
consume channel
receive ident from channel then branch
suppress lintName because "reason" in statement
skip
$stmt(term)
```

`$stmt(term)` expects `Act`. It is deliberately distinct from `$(term)`,
which expects `Expr w`; expression and statement escapes never blur.

`let` is a pure hygienic expression alias scoped over the remaining statements
in its enclosing brace block or rule. It lowers to a Lean `let` around the
rest of the constructed `Act`; it declares no register or wire, performs no
write, and does not promise that synthesis will share the resulting logic.
The inferred form is accepted when the initializer determines one unambiguous
`Expr w` or packed-expression type. A literal-only or otherwise width-ambiguous
initializer uses `let mask : 8 := 255`. A local may shadow an imported helper
but not a design-local signal, endpoint, generate binder, or another live
hardware local. This gives large FSM arms a visually continuous name for a
shared expression without turning a module-internal convenience into an
output port or opaque `$()` escape. The no-sharing/cost note belongs in the
first tutorial use and is available as an informational lint.

All semantic lints run on the hygienically expanded/lowered action, so `let`
is transparent to them. In `a <- b; let x := a; c <- x`, the start-of-cycle
read warning points at the later `x` use and names its `a` initializer, exactly
as if the later expression had named `a` directly. A local used five times is
notation and may initially inline five expression trees; `DagEval` and compilation may recover structural
sharing, but the source `let` neither declares one wire nor promises one RTL
net. Authors wanting a named observable combinational signal use `output wire`.
Because lowering erases aliases, the delaborator never reconstructs a `let`;
round-trip structural tests compare its inlined core form and this is not a
pretty-printer defect.

Logical channel vocabulary is intentionally behavioral rather than
signal-level. Its v1 syntax-to-core and behavioral contract is:

| Surface | Core | Cycle-level meaning |
| --- | --- | --- |
| `q.canSend` | `q.canEnq` | The generated source endpoint can accept a new payload on this island cycle. |
| `send value to q` | `q.enq value` | If `canSend`, write the endpoint payload and mark it valid; otherwise do nothing. |
| `send value to q then body` | guarded `q.enq value`; `body` | If `canSend`, enqueue exactly once and execute the body; otherwise do neither. |
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
An enabled-by-default informational lint points at any `send` not syntactically
dominated by the same channel's `q.canSend` guard and explains that the payload
may be dropped while later statements still execute. “Dominated” has one
deliberately decidable meaning: some enclosing `if` branch condition contains
that exact `q.canSend` expression as a positive conjunct, either alone or in
an `&` tree with other terms. Negation, disjunction, another channel's guard,
`q.hasData`, or user-maintained shadow state does not qualify. Semantically
correct shadow tracking may therefore warn; that is preferable to pretending
the syntax checker proved a protocol invariant. Likewise, reading `q.data`
without the same channel's positive dominating `q.hasData` conjunct receives
a teaching warning. A `receive` body is structurally guarded for its receive
channel, but does not guard sends or reads on any other channel. The logical
runner currently supplies zero for an empty queue, while a physical storage
realization may retain an old sample; neither value is a payload guarantee,
and portable code must not observe it.

All informational semantic lints use one per-statement suppression form:

```text
suppress unguarded_channel because "intentional best-effort telemetry" in
  send sample to telemetry
```

The same form and required nonempty reason string applies to
`read_after_write` and `multiple_write`. It suppresses only the named finding
at that statement and remains visible in inspection metadata. It cannot
suppress structural errors such as two possible sends/consumes to one endpoint
in an event.

The canonical producer form is the symmetric guarded transaction:

```lean
send 42 to q then {
  sent <- 1
}
```

It lowers once to `Act.ite q.canEnq (Act.seq (q.enq 42) body) Act.skip`.
Consequently both the endpoint write and every body update occur only when the
source endpoint can accept the value. Body reads retain ordinary start-of-
cycle semantics, and a second send to `q` in the body remains a structural
error. Bare `send` is the explicit best-effort/advanced form and retains its
enabled-by-default warning.

`Chan.exchange` and `Chan.refusePush` describe a full queue when producer and
consumer are accepted on the same named-clock event. `exchange` accepts the
push after removing the old head; `refusePush` rejects it. `Clock.asynchronous`
admits coincident unrelated edges, so a channel between distinct domains can
encounter that co-tick case. Only the deliberately narrower
`Clock.interleaved` proof relation excludes it. The default policy and this
distinction must both appear in generated documentation and executable tests.

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
or conditionally defer the visible head, but tutorials and ordinary examples
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

The escape contract is proof-carrying rather than an unchecked annotation or
open-ended typeclass. There is one authoritative core function on `Act` that
computes branch-sensitive endpoint transaction bounds; both closed-term
checking and open-term proof obligations refer to that definition. A second
summary semantics is forbidden. `$stmt(term)` accepts an ordinary `Act` only
when its closed lowered tree is analyzable and contains no opaque endpoint
access. For open or irreducible parameterized actions it also accepts an
ordinary library wrapper `EndpointAct` containing the `Act`, an
`EndpointFootprint`, and a theorem that the summary bounds the result of that
same core footprint function. A plain syntax annotation is insufficient
because a false footprint could permit data loss.

Ordinary authors using direct syntax do not write these proofs. Public
`EndpointAct.send`, `.consume`, `.ite`, and skip-composition builders compose
the action, footprint, and proof together. Sequential composition additionally
requires only an `EndpointAct.Disjoint` witness: for every endpoint, one side
has zero transactions. This obligation is unavoidable for genuinely open
channel parameters because two Lean arguments may alias the same run-time
channel even when their binder names differ; silently assuming distinctness
would make the one-transaction guarantee false. Concrete/reducible actions
discharge it with `simp`/`decide`, while the builder derives the full footprint
centrally. `ite` takes branch maxima, and a generated list fold adds every
iteration. Thus a send inside an `n`-element generated loop correctly has bound
`n` and is illegal for one endpoint when `n > 1`. If a splice supplies a bare irreducible `Act`, the source
diagnostic explains Loom's one-transaction-per-endpoint rule and names
`EndpointAct` and its builders instead of exposing a typeclass or metavariable
failure.

The same rule governs `for ... generate`: a reducible list is expanded and
counted normally; an irreducible collection whose body may transact is
rejected unless the surrounding escaped `EndpointAct` proves the required
per-event bound. This is the explicit meeting point between arbitrary Lean
parameterization and command-time endpoint checking, and it must exist before
channel syntax ships. Before freezing the wrapper interface, prototype it
against the LNP64mini telemetry island and a deliberately parametric example
that operates on several distinct channels; revise the wrapper if either use
requires hand-authored routine footprint proofs.

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

For an ordinary `Expr w`, `default` is required unless the distinct labels
cover all `2 ^ w` values. For a declared `states` register, listing every
declared member is source-level exhaustive and the elaborator inserts the
documented `default => skip` for unused encodings. If a genuinely bit-total
ordinary case also supplies `default`, the command accepts it but warns that
the branch is unreachable; a non-final default remains an error.
Exhaustiveness is computed from normalized values and registered enum metadata,
never guessed from spelling or an invariant.

This construct is v1-adjacent: it should land before using an FSM-heavy
LNP64mini block as an integration example even if the scalar tutorial ships without it. Its release is also
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
let                   -> hygienic Lean let around the remaining Act
case                   -> a source-ordered, right-nested Act.ite chain
for/generate           -> an ordered Lean List fold using Act.seq
bare send/consume      -> Chan.enq / Chan.pop
send ... then          -> one guarded Chan.enq/body action
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
literal 300 does not fit in 8 bits; expected 0 through 255
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
const name : width := constant-value
states name : { State0, State1, ... }
states name : { State0, State1, ... } := reset-state
states name : width { State0, State1, ... } := reset-state
output states name : { State0, State1, ... } := reset-state
output states name : width { State0, State1, ... } := reset-state
```

The width position is a Lean `Nat` term rather than a Verilog-style `[hi:0]`
range. Consequently `reg pc : 64` and `reg idx : addrW` are direct spellings;
an inline compound term is parenthesized, as in `reg lane : (bytes * 8)`, to
keep packed type names and following declaration syntax unambiguous. All three
forms reduce through the same checked width path. Widths must reduce far enough
to construct the indexed handle and declaration, and a zero width receives a
direct warning or error according to the core policy established in Phase 0.

`input reg` is not accepted because it lies about writability. `output wire`
is a distinct combinational-output production: its RHS elaborates as
`Expr width`, lowers to `Declarations.addCombOutput`, and generates a readable
`Expr width` definition for reuse. It has no `Reg` handle and cannot appear on
the left of `<-`; `Design.cycle` is unchanged. V1 deliberately rejects
`output wire done := count == 255`: even when inference looks obvious, the
declaration block is the module interface and must expose every port width
without elaborating its implementation expression. A register initializer is
declaration syntax, not `hwexpr`: it elaborates with expected type
`BitVec width` and becomes the `RegDecl.init` value. Numeric literals, local
`Nat`s, and `@[hw_const]` declarations use the expected width only after the
same `n < 2 ^ width` range check as runtime expressions, so
`reg pc : 8 := 300` is an error rather than reset-to-44 while
`reg pc : 64 := TEXT_BASE` needs no annotation. An arbitrary computed reset
image uses an explicit Lean escape returning `BitVec width`; that explicit
term is the only place an author may deliberately construct a modular value.
This keeps reset values separate from expressions over pre-cycle state and
same-cycle observations.

`const` is the ordinary design-local spelling for state codes, masks, command
numbers, and fixed shifts:

```lean
const CMD_QUANTUM : 7 := 72
const WRITE_CMD : 8 := 0xA3
```

Its value must be a reducible nonnegative compile-time constant, is
range-checked once against the declared width, and lowers to one generated
`Expr.lit` definition. It creates no port, register, wire, or RTL declaration.
The name participates in the design-local table and delaborates by name. Like
every generated local Lean definition, it cannot duplicate a signal or another
local declaration. Any unique design-local declaration—signal, local constant,
or state member—wins over an opened external `@[hw_const]` with the same short
name; within the design, collisions are errors rather than shadowing. Thus the
existing signal-first safety rule is preserved and local constants add no
ambient ambiguity surface. `@[hw_const]` remains only for deliberately shared
cross-design `Nat` constants and should not appear in beginner material.

`states` is enum metadata over an ordinary register and literal encodings, not
a new value type or transition semantics:

```lean
states st : { S_F0, S_IC, S_EX, S_PAUSE, S_GRET } := S_F0
```

Members receive declaration-order encodings `0 .. count-1`. The inferred width
is `max 1 (ceilLog2 count)`; an explicit width is accepted only when every
encoding fits. Empty and duplicate member lists are errors. Omitting the reset
initializer selects the first member, matching the core register's zero reset,
but canonical `#show_hardware` prints that reset explicitly so it is never
hidden during review. The command generates the ordinary `Reg width`, one
typed local literal per member, encoding/name metadata, and simplification and
case-split support whose branches retain member names. It also generates the
explicit predicate “the register holds a declared member.” The unconditional
split includes a named illegal-encoding branch; given that predicate as an
invariant, the companion split lemma produces only the declared member
branches. `output states` differs only by adding that ordinary register to the
declared output set; it does not change enum or transition semantics.

A `case st` that lists every declared member may omit its source `default`.
The lowering still inserts `default => skip` for unused bit encodings, and
`#show_hardware` displays that implicit illegal-encoding behavior. Reachability
of only declared states is an invariant obligation, not a parser claim. An
explicit default remains available when a design deliberately recovers from
an illegal encoding. In expressions and proof presentation, an exact member
encoding prints as `S_IC` when the expected enum metadata identifies `st`;
otherwise delaboration conservatively prints the underlying typed literal.

The command creates handles, rule bodies, `declarations`, and `design` in the
current namespace. It uses `withRef` and declaration ranges based on the user
tokens so go-to-definition and generated-code failures return to the DSL
source.

This flat naming is intentionally different from `system` qualification in
v1. `hardware satcounter` preserves the current handwritten Lean API
(`count`, `tick`, `design`) and therefore enables the tutorial and existing
proofs to migrate without renaming; its cost is one hardware design per Lean
namespace. A `system` necessarily creates many islands, channels, and generated
components under one command, so its command identifier is a real namespace
key and its public children are dot-qualified. V1 will not silently change the
hardware convention after users adopt it. After the compatibility migration,
an opt-in qualified hardware form may be evaluated as a separate versioned
surface, with generated compatibility aliases and an explicit deprecation
period; it is not folded into the initial syntax work.

One `NameSet` covers every Lean name the command will generate:

- signal and memory handles;
- design-local constants, state registers, state members, and enum metadata;
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

The per-statement suppression syntax also has one rule-level form for this
pattern:

```text
rule pulse_defaults suppress multiple_write because
    "later rules intentionally override one-cycle defaults" := {
  ...
}
```

It suppresses only findings of the named informational lint originating in
that rule and retains the reason in metadata. Per-statement suppression remains
the recommended narrow form. Rule-level suppression cannot hide endpoint
transaction errors, width errors, or findings in later rules, and no
`defaults` keyword or altered write semantics is introduced.

These findings are informational lints, not proof obligations or semantic
checks. Intentional sites use the single
`suppress lint_name because "reason" in statement` form defined above; the
reason is retained in inspection metadata. Generated or highly parametric
`$stmt(...)` actions may fall back to the same core footprint analysis used by
the endpoint checker instead of pretending the surface command can see through
arbitrary Lean. The authoritative semantics and compiler checks remain
unchanged.

### Diagnostic voice

Every diagnostic follows one voice: (1) what Loom found, (2) why that reading
is rejected or risky, and (3) the concrete source rewrite when one exists.
The important repair cases include:

- parenthesize either plausible grouping for a forbidden operator mixture;
- insert the appropriate explicit `zext` or `sext` candidate for a width
  mismatch, without guessing signedness silently;
- rewrite a bare send into a guarded-transaction skeleton or an explicit
  `canSend` guard without silently moving neighboring statements into it;
- insert `default => skip` when a non-enum `case` is incomplete; and
- insert the common suppression form with an editable required-reason field.

Ambiguous choices are shown as separate rewrites rather than one preferred
guess. Golden diagnostics check message voice, source spans, suggested source,
and that each advertised rewrite elaborates to the expected core term. All
required feedback is ordinary compiler output and inspection-command text.

### One-cycle teaching view

The syntax layer exposes a non-semantic teaching command:

```lean
#trace_cycle counter with { enable := 1 } from { count := 254 }
```

It traverses the already-lowered rules in source order, evaluates guards and
writes against the ordinary start-of-cycle state/ordered accumulator, and
prints each fired write as `old -> new`, including later overrides. Its final
state is checked against the existing evaluator result; the command introduces
no second transition semantics and is not a proof or certified simulation API.
It is the tutorial answer to pre-cycle reads and last-write-wins, including the
`pulse_defaults` pattern.

`from { ... }` is a partial override of `design.reset`; `with { ... }` is a
partial input environment whose omitted inputs are zero, matching the existing
closed teaching-run convention. Unknown names, writes to inputs in `from`,
state names in `with`, and out-of-range values are source-local errors. The
header prints that reset/zero-default convention so a short example never
hides its initial conditions.

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

Ordinary proof-state unexpanders do not re-elaborate and compare every printed
term at display time; doing so would make large goals pay an unpredictable
rendering cost. Production safety comes from a conservative structural
printer: it emits a wrapper only for constructor shapes whose inverse is
obvious and otherwise immediately falls back to core notation. The exhaustive
print/reparse/core-equality matrix is enforced in the test suite for every
supported shape and every precedence boundary. `#show_hardware`, by contrast,
is an explicit inspection command and performs its advertised structural
round-trip check before labeling a whole `Design` as pretty hardware. Thus a
future unexpander drift is caught by gates without turning interactive pretty
printing into a hidden elaboration loop.

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

### Executable single-design surface

Single-clock authoring gets the same lightweight inspection symmetry as a
system without replacing the tutorial's differential harness:

```lean
#run_hardware design for 10 cycles
#run_hardware design for 10 cycles inputs $(inputTrace)
```

The command elaborates its subject as an existing `Design` or
`CertifiedDesign`, starts from that design's reset state, and delegates to the
existing `Design.run`/`runOpen` or certified verified-simulator path. The input
escape has the existing typed input-trace shape; no second trace model is
introduced. Its default display shows declared outputs and applied input
samples, with an option to name additional registers through existing typed
handles. It is a convenience for “watch this hardware run,” not a replacement
for `Loom.Runner` differential oracles and not a new executable semantics.

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
      if ~sent then
        send 42 to q then
          sent <- 1

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
Clock.alignGroups relation groups
                              -- add aligned clock groups to a base relation
```

The `clocks` item elaborates its argument with expected type `ClockRel` under
generated clock-handle locals. A simple qualified name/application needs no
escape; arbitrary Lean computation uses `$(term)`. The mechanical
`.unconstrained` name is not exposed as a second stock alias because it is
currently definitionally the same relation as `.asynchronous`; two names would
imply a distinction that does not exist. A project may define another
`ClockRel` library value without extending grammar or creating a second
schedule language.

The first realistic three-clock case must not hit an undocumented escape
cliff. The stock library therefore includes a composition combinator whose
meaning is “apply these alignment constraints; retain the base relation for
everything else.” Because this is ordinary Lean composition rather than
fundamental grammar, a mixed topology is written explicitly through the term
escape:

```lean
clocks $(Clock.alignGroups Clock.asynchronous
  [[cpu_clk, bus_clk]])
```

Here `cpu_clk` and `bus_clk` are aligned with one another, while `debug_clk`
and every other pair retain the base relation's asynchronous/coincident-edge
behavior; unlisted clocks are implicit singleton groups. Within each listed
group, an event is accepted only when either every clock fires or none does.
Distinct groups retain the base relation between them.

The well-formedness rules are fail-closed and source-local: an empty group is
an error; a repeated clock within one group is an error; a clock occurring in
two groups is an error pointing at both occurrences rather than silently
merging groups; an undeclared clock is an error; and a singleton group is
accepted with an informational “redundant; unlisted clocks are already
singletons” warning. The tutorial may start with the two-clock aliases, but the
first SoC example must show this escaped composite and its `#show_system`
rendering.

Alignment constrains proof schedules; it does not choose a circuit or certify
a physical clock relationship. Two aligned but distinctly named clocks still
require an explicit cross-clock realization and cannot select
`Cdc.synchronousFifo`, whose certification requires clock-name equality. Its
diagnostic says: “alignment is a schedule assumption, not a timing-closure
fact; the synchronous realization requires one shared physical clock. Select
a certified crossing realization or use the same clock handle.”

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
ordinary `Design` before endpoint generation; it permits focused extensions of
a large existing design without requiring a source rewrite. The plain `:=` form uses an existing `Design`
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
- an unguarded `send` explains that a full channel drops the payload and does
  not guard following state updates, and points to the narrow best-effort
  suppression when that behavior is intentional;
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

The two-clock tests pin the channel vocabulary before it freezes. Its normal
producer uses `send ... then`; bare best-effort send appears only in the
deliberate contrast. Executable cases cover an unavailable send, an empty
`q.data` read, the cycle in which `consume` takes effect, a full-queue co-tick
under both policies, and whether a statement following each send form is
acceptance-guarded.

## Representative LNP64mini integration

The following is a representative final-form excerpt based on the actual
LNP64mini trace ring, registered memory reads, pulse defaults, quantum counter,
and domain observation. It shows the intended reading experience; the exact
memory and register-family declaration spellings are a v2 design task below.

```lean
import Loom.Hw.Dsl
import Machines.Lnp64mini.Interface

namespace Machines.Lnp64mini

open Loom.Hw

hardware lnp64mini where
  const TEXT_BASE : 64 := 0x0000_0000_0000_1000
  const CMD_QUANTUM : 7 := 72
  const READY : 5 := 1
  const FUTEX : 5 := 3

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
  output states st : 5 {
    S_IDLE, S_F0, S_FW, S_EX, S_L0, S_L1, S_TRAP, S_DL,
    S_DST, S_DSW, S_WAIT, S_CLONE2, S_FTX1, S_MUL, S_RD, S_RD2,
    S_DIV, S_PAUSE, S_CLONE3, S_GPL, S_GPS, S_IC, S_GC0, S_GC1,
    S_DC, S_CS0, S_CS1, S_CR0, S_CR1, S_GRET
  } := S_IDLE

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
every member of a declared `states` register may omit it, with the generated
illegal-encoding arm remaining an explicit skip in inspection.

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
`mDonePort`/`mDone`. Representative conversions retain compatibility aliases
and prove exact lowering. Collapsing those pairs is a separate Lean source-API
decision and is not required by this plan; the syntax must not add an alias
field merely to reproduce existing naming scaffolding.

## Memory and register-family extension

The scalar command is sufficient for the tutorial, while realistic integration
examples also exercise `Mem`, `RegArray`, initialization, and memory
implementation policy. Those constructs need one coherent grammar independent
of whether any existing large design is rewritten wholesale.

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
   blocks, local expression `let`, the complete precedence table and forbidden
   comparison/bitwise, shift/arithmetic, and concatenation/infix mixtures,
   plus direct comparison-chain rejection, design-local `const`, declared
   `states`, guarded `send ... then`, `case`, `for ... generate`, explicit
   memory ports, packed struct declarations/literals/updates, quotations inside
   Lean functions, and both escape categories.
4. Decide ASCII spellings for signed/unsigned comparison and bitwise operators
   before any public parser surface ships.
5. Settle zero-width policy and freeze the no-truncation rule for source
   literals, lifted locals, `@[hw_const]` declarations, and reset values. Test
   the exact distinction between declaration reset values and runtime
   expressions. Freeze the `case` rules above:
   normalized duplicate rejection, finite exhaustiveness, optional default
   only for total coverage, and a dead-default warning.
6. Freeze identifier resolution examples covering a design-local signal that
   shadows an imported `@[hw_const]`, two deliberately registered constants
   with one short name, a hygienic local `Nat`, an unrelated unmarked `Nat`
   that cannot affect an existing body, and explicit fully qualified
   disambiguation.
7. Record the exact shift contract from the core: equal-width unsigned count,
   logical right shift, width-preserving result, and zero for an out-of-range
   count. Keep arithmetic shift and mixed-width shift syntax omitted, list
   `>>s` explicitly among omitted constructs, and document/test the
   sign-extend/logical-shift/slice helper idiom.
8. Freeze decimal/hex/binary literal spelling and canonical fallback
   delaboration, including underscore separators and exact range checking.
9. Freeze the diagnostic voice, textual repair guidance, `#trace_cycle`
   output, and statement/rule lint suppression forms before messages
   proliferate across phases.

### Phase 1: wrappers and scalar expression/statement syntax

1. Add a syntax module that imports only the existing authoring core.
2. Declare `hwexpr` and `hwstmt` plus `[hwexpr| ...]` and `[hwstmt| ...]`.
3. Implement pure constructor lowering with macros.
4. Implement `<-`, range-checked literal lifting, `@[hw_const]`, deliberate
   identifier resolution, and escape elaborators with expected-type
   propagation.
   Accept decimal/hex/binary spelling and static `Nat` shift amounts without
   changing the equal-width core constructor.
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
11. Add hygienic pure `let` bindings with inferred and explicit-width forms,
    lexical scope, collision checks, lint-transparent lowering, no implied
    hardware-sharing promise, and an explicitly inlined delaboration contract.
12. Add the shared informational-lint suppression wrapper and diagnostic/code-
    action infrastructure; individual lints register with that one surface.

### Phase 2: scalar `hardware` command

1. Parse declaration-first scalar inputs and registers followed by rules.
   Include width-typed design-local constants and declared state sets before
   rules; generate only ordinary literals, registers, metadata, and lemmas.
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
10. Add `#trace_cycle` over lowered command metadata, checking the teaching
    trace's final state against the existing evaluator.

### Phase 3: proof presentation

1. Add the scoped environment extension keyed by the full generated `design`
   constant name.
2. Implement `hw_unfold design` as a fixed tactic using per-design metadata.
3. Add conservative expression and action unexpanders that produce wrappers.
4. Keep read-collapsing local to wrapper reconstruction.
5. Confirm that partially simplified expressions fall back cleanly to core
   notation rather than printing invalid DSL.
6. Add `#run_hardware` as presentation over existing single-design reset/run
   and open-input APIs; keep the existing differential runner separate.

### Phase 4: tests before migration

Add positive elaboration and structural equality tests for every production,
then golden diagnostic tests for:

- flat `else if` ownership and rejection of an unbraced nested `if` branch;
- sequencing and empty/nested brace blocks;
- every precedence boundary; legal arithmetic-before-comparison; postfix over
  prefix (`~x[3]`); comparison non-associativity including width-one chains;
  and source-local rejection of unparenthesized comparison/bitwise,
  shift/arithmetic, and concatenation/infix mixtures in both orders;
- shift RHS width, unsigned-count behavior, logical-right-shift behavior,
  direct static `Nat` amounts, dynamic-width mismatch, and out-of-range counts,
  plus a diagnostic/idiom for omitted `>>s`;
- writes to inputs;
- writes to combinational outputs, and same-cycle evaluation of valid
  `output wire` observations without changing `Design.cycle`;
- target/RHS and splice width mismatches;
- register reset-value width mismatches and literal overflow in reset/runtime
  positions, including lifted locals and `@[hw_const]` values; negative-literal
  all-ones guidance; irreducible constants failing closed; and rejection of
  `@[hw_const]` on a non-`Nat` declaration; plus rejection of an unsized
  literal in a still-width-polymorphic standalone quotation;
- decimal, hexadecimal, and binary literals with separators, identical
  normalized values/range failures, source-radix preservation, and canonical
  fallback delaboration;
- invalid widths and dynamic slice/bit-select attempts, including the
  shift-and-static-select suggestion;
- non-exhaustive `case` without a default;
- exhaustive `case` without a default (accepted) and with a dead default
  (warning);
- duplicate `case` labels both textually and after normalization;
- non-final default and a pattern of the wrong width;
- design-local signal precedence over an opened imported `@[hw_const]`, an
  imported-but-unopened constant remaining ineligible, and scope activation;
- ambiguity between deliberately registered non-signal candidates, plus fully
  qualified disambiguation and immunity to an unrelated unmarked `Nat`;
- inferred and explicitly typed local `let`, lexical scope, hygienic capture,
  width ambiguity, signal-name collision, lint transparency, inlined
  round-trip form, and the no-sharing cost note;
- local constants: declaration-time range checking, collision behavior,
  named delaboration, and absence from RTL state and ports;
- declared states: inferred/explicit width, empty/duplicate/capacity errors,
  default-first and explicit reset, ordinal encodings, member-named proof
  branches, exhaustive source cases with visible illegal-encoding skip, and
  explicit illegal-state recovery;
- empty, singleton, and nested `for ... generate` bodies;
- generated write ordering, including two iterations writing the same target;
- a hygienic generate binder that shadows an imported non-signal name without
  capture, and rejection when it collides with a design-local signal;
- static `Fin` family indexing versus dynamic `Expr` indexing, including the
  informational cost diagnostic;
- quotations embedded in Lean functions, maps, folds, and reusable actions;
- `#run_hardware` agreement with the existing closed/open single-design run
  paths and rejection of a mismatched input trace;
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
- exact per-channel positive-conjunct dominance for `canSend`/`hasData`,
  including wrong-channel guards, shadow state, disjunction, and a send inside
  an unrelated receive body; and
- the shared required-reason suppression form at an intentional site without
  suppressing other findings or structural endpoint errors;
- rule-level suppression scoped to one named lint and one rule; and
- diagnostic spans and textual rewrites for parentheses, extension, guarded
  send, missing default, and suppression, with successful re-elaboration.

Teaching-view tests compare `#trace_cycle`'s final state with the existing
evaluator and pin rule-order guard/write output for pre-cycle reads and
last-write-wins.

Proof-shape tests lower an FSM-sized `case` and exercise the standard invariant
workflow with the tactics used elsewhere in Loom. They record goal count,
nesting, and whether branch hypotheses retain recognizable case labels. `case`
does not graduate from v1-adjacent status until this is usable. If ordinary
splitting is not sane, add and test per-rule case-split metadata/lemmas before
using an LNP64mini FSM block as the representative integration case; do not
leave that repair to individual proofs.

Packed proof-shape tests similarly lower representative whole-value plus
partial-field updates, conditional disjoint field writes, and ordered
overlapping writes, then exercise the ordinary invariant/simplification
workflow. They record whether bounded `writeSlice` merge terms reduce to
recognizable field facts without manual bit arithmetic. Packed partial
assignment does not graduate to v1 until these goals remain usable; if not,
add layout-aware generated lemmas/tactics before migrating a real bundle.

Round-trip tests parse each supported expression and action, delaborate it,
reparse the wrapper, and compare the lowered core term. Separate negative tests
ensure ordinary `Reg.rd` terms outside wrappers are not collapsed. These tests,
not print-time re-elaboration of every proof state, enforce ordinary
unexpander faithfulness; explicit `#show_hardware` retains its runtime
whole-Design structural check.

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
8. Pass the packed partial-write proof-shape gate above, adding layout-aware
   simplification support if ordinary invariant goals expose raw nested merge
   terms.
9. Run the packed golden matrix above and convert one real LNP64mini request or
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

1. Freeze the channel syntax-to-core table, unavailable-operation
   behavior, invalid-empty-data rule, and full co-tick policy examples before
   adding productions.
2. Add channel observations/statements to `hwexpr`/`hwstmt`, lowering only to
   the existing `Chan.canEnq`, `canDeq`, `deq`, `enq`, and `pop` definitions.
   Make `send value to q then body` the canonical producer form: one `canEnq`
   guard encloses both the enqueue and body. Retain bare send as the warned
   best-effort form.
   Include canonical `receive value from q then body` as hygienic syntax for one
   `canDeq` guard, one bound `deq`, the body, and one appended `pop`.
3. Implement branch-sensitive send/consume footprint checking over lowered
   actions. Point at both sites for a sequential or cross-rule conflict, and
   require analyzable metadata from statement escapes that touch endpoints.
   Define the proof-carrying `EndpointAct`/`EndpointFootprint` wrapper and its
   compositional library combinators first; do not use an inferred typeclass or
   trust a syntax-only footprint assertion. Reducible generated lists are
   counted directly, while irreducible parameterized endpoint actions require
   this wrapper or are rejected.
   Both interfaces must use one core `Act` footprint function. Supply
   proof-carrying send/consume/sequence/conditional/fold builders whose routine
   obligations close by construction, and prototype the API against the
   LNP64mini telemetry island plus a parametric multi-channel example before
   freezing it.
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

Channel/system golden diagnostics cover unguarded `data`; unguarded `send`, its
best-effort suppression, exact same-channel conjunct dominance, wrong-channel
and receive-body counterexamples, a correctly dominated send, and guarded
`send ... then` executing both-or-neither; double send/consume;
`receive` binding scope, empty-channel no-op behavior, and exactly one appended
consume; unanalyzable endpoint escapes; handles outside an extended Design;
duplicate or unused clocks, channels, and islands; malformed global/pairwise
clock relations; mixed-topology `Clock.alignGroups` composition, empty and
overlapping groups, duplicate/undeclared clocks, redundant singleton warning,
and rejection of a synchronous FIFO between aligned-but-distinct clock names;
missing or repeated connections; wrong endpoint
direction; undeclared clock use; missing reset policy; malformed
width/depth/policy;
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
   Ordinary proof-state unexpanders remain conservative and rely on the gated
   round-trip matrix rather than reparsing every displayed term.
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
3. Pin unavailable sends, empty data, consume timing, an aligned variant's
   full co-ticks under both policies, and neighboring statements that are not
   acceptance-guarded with executable semantic tests.

### Phase 11: SoC Fabric Gauntlet usability validation

The existing gauntlet is a deliberate structural-compatibility gate, not a
blind source rewrite. Its islands currently pre-apply endpoint adapters in a
machine-specific nesting order that is neither connection order nor its global
reverse. The `system` command correctly derives adapters from declared
connections, so migrating those island bodies today would change the exact
`Design` trees and invalidate proof/artifact equalities even if behavior were
later shown equivalent. Do not weaken those equalities. Migrate the gauntlet
only after either (a) its evidence is intentionally regenerated and the
structural change is reviewed, or (b) a general, user-natural adapter-order
contract is designed from more than this one compatibility case. A hidden
gauntlet-specific lowering switch is out of scope.

The completed SoC Fabric Gauntlet is the preservation baseline for this phase.
Its canonical RTL SHA-256 is
`33335f3f906ccb427476d20dd5a7ea718cd7559c249b21802803b419fa1748ac`, and both
the formal and FPGA evidence manifests verify. A syntax-only conversion must
retain that byte identity; a mismatch stops the conversion for explicit
semantic/artifact review rather than regenerating evidence under this plan.

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
7. Require `#show_system` and the source itself to expose each arbitration
   point, CDC route, backpressure path, reset loss behavior, and
   target-specific assumption without requiring inspection of generated Lean.

This phase validates syntax and naming only. It does not make the pretty plan
responsible for the gauntlet's hardware, proofs, FPGA campaigns, or evidence
model.

### Phase 12: representative LNP64mini validation

LNP64mini is an integration test, not a migration deliverable. Keep a small,
coherent set of real blocks in readable syntax: declaration families, pulse
defaults and observation rules, trace/registered-memory traffic, at least one
FSM arm, a generated thread-table action, and the telemetry `system` surface.
This is enough to exercise the difficult language boundaries against a
production-scale consumer. Do not convert the remaining core merely to raise a
syntax-adoption percentage.

Every syntax-only block that is touched must retain its compatibility aliases
and prove equality of the lowered `Design` or an equivalent structural
characterization, plus deterministic byte-identical emitted RTL. Run the
relevant existing `DesignWF`, sync-read, evaluator, behavioral, and
board-facing gates in proportion to the touched block. A difference stops that
conversion for review. Alias retirement remains a separate Lean API project,
outside this plan.

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
2. Every supported token has a documented one-to-one core meaning and the
   public precedence contract fixes postfix/unary/arithmetic/comparison order,
   rejects comparison chains directly, and requires parentheses for
   comparison/bitwise, shift/arithmetic, and concatenation/infix mixtures whose
   intended grouping is not universal.
3. Width, mutability, collision, and static-slice errors point at user syntax;
   source literals and lifted `Nat`s are range-checked and never truncate
   silently.
4. Wrapped delaborator output reparses to the same core term in the gated
   matrix, while production unexpanders conservatively fall back without
   reparsing every displayed goal.
5. Importing lower-level hardware modules does not activate the new syntax or
   pretty-printers.
6. `hw_unfold` is isolated per fully qualified design.
7. A representative LNP64mini block reads in the form shown above while its
   generated simulator, proof obligations, and checked RTL path remain
   unchanged.
8. LNP64mini is not required to migrate wholesale. Every representative block
   converted under this plan preserves its existing Design and emitted RTL;
   unrelated constructor-heavy code may remain unchanged.
9. Executable teaching tests and golden diagnostics pin assignment timing,
   branch ownership, widths, signedness, memory-port behavior, and Loom's
   source-ordered meaning of `rule`.
10. `case` rejects normalized duplicate labels, handles exhaustive/default
    behavior as specified, and has a tested proof workflow on an FSM-sized
    rule rather than merely acceptable parser output.
11. Bare identifiers follow the documented signal-first, unique-candidate
    resolution rule; only hygienic locals and deliberately registered and
    opened-scope `@[hw_const]` global `Nat`s lift automatically. Attribute
    targets are validated, values reduce and range-check fail-closed at every
    use, and adding or merely importing an unrelated declaration cannot change
    an existing netlist expression.
12. Parameterized hardware keeps its generated body visible through
    quotations and `for ... generate`; Lean maps, folds, functions, and
    recursion compose with those quotations while lowering to the unchanged
    finite `Expr`/`Act` core. Irreducible endpoint actions carry a proved
    `EndpointFootprint` through `EndpointAct` rather than bypassing static
    send/consume bounds.
    The closed checker and `EndpointAct` theorem use one core footprint
    definition, ordinary builders discharge routine proofs, and both the
    LNP64mini telemetry and a parametric multi-channel example use the API
    without hand-authored boilerplate proofs.
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
    full co-tick behavior above; canonical `send ... then` makes enqueue and
    producer updates both-or-neither, canonical `receive` structurally guards
    data and appends exactly one consume, bare send is visibly best-effort, and
    the command rejects more than one possible send or consume per endpoint
    event with branch-sensitive locations.
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
    and checked runners, while `#run_hardware` delegates to the existing
    single-design semantics/verified runner. Executable tests pin acceptance,
    payload-validity, and consume timing.
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
    independently meaningful rule `Act`s, keep every RHS read pre-cycle, and
    pass an FSM-scale invariant proof-shape gate without exposing raw merge
    arithmetic as the normal user workflow.
26. V1 rejects implicit whole-record arithmetic, incomplete literals, and
    unsupported aggregate kinds rather than inventing semantics, and its vector
    RTL remains structurally/byte equivalent to the corresponding handwritten
    packed core design.
27. Every pretty `system` explicitly names its logical reset policy, while
    derived electrical reset behavior appears in `#show_system` rather than as
    fake configurable syntax; independent flush requires recoverable
    realizations and coordinated reset never silently selects them.
28. Mixed clock topologies use an ordinary `Clock.alignGroups` library
    combinator over a named base relation, are shown in the first SoC example,
    reject duplicate/overlapping membership, treat unlisted clocks as
    singletons, and require no pair-specific grammar expansion. Alignment never
    authorizes a same-clock physical realization between distinct clock names.
29. Local hardware `let` bindings are hygienic pure aliases with explicit
    lexical scope, transparent lint analysis, inlined delaboration, and no
    implied register, output port, net, or synthesis-sharing semantics.
30. Representative syntax-only LNP64mini blocks preserve compatibility aliases
    and exact RTL; neither full-source conversion nor alias retirement is a
    prettification completion gate.
31. Design-local `const` makes the common fixed-code path width-typed,
    range-checked once, named in goals, and absent from generated state/ports;
    beginner examples need no `@[hw_const]` ceremony.
32. `states` generates only an ordinary register, literals, metadata, and
    lemmas; inferred/explicit widths are checked, member-total source cases may
    omit a default, and inspection always exposes the generated skip behavior
    for illegal encodings. Reachability remains an ordinary invariant.
33. Decimal, hexadecimal, and binary literals with separators share one exact
    range check and have a stable source-aware/canonical delaboration policy.
34. Static shifts accept compile-time values directly while dynamic amounts
    retain the core's explicit equal-width type and cost visibility.
35. Every mechanically repairable rejection follows the common diagnostic
    voice and supplies tested textual repair guidance; informational findings
    share one reason-required statement/rule suppression mechanism.
36. `#trace_cycle` agrees on final state with the existing evaluator and shows
    source-order fired writes without defining new semantics.
37. Output/interface widths remain explicit even when an RHS would make them
    inferable, and no `defaults` keyword or special write semantics is added.
