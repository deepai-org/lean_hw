# Pretty Loom hardware DSL

This document is the implementation plan for a readable, Verilog-shaped
authoring layer over Loom's existing hardware EDSL. The destination is concise
hardware code that remains an ordinary shallow embedding: syntax elaborates to
the current `Expr`, `Act`, `Reg`, `Mem`, `Declarations`, and `Design` values,
and the kernel, semantics, compiler, verified simulators, and emission boundary
do not acquire a second representation.

The purpose is not to accept Verilog. It is to make Loom hardware immediately
legible to a Verilog engineer while preserving the places where Loom's model is
deliberately different: rules instead of event controls, nonblocking writes,
explicit signedness, typed widths, and ordinary Lean as the parameterization
language.

## Outcome

The tutorial's saturating counter should eventually read:

```lean
import Loom.Hw.Dsl

namespace Machines.Tutorial.SatCounter

open Loom.Hw

hardware satcounter where
  output reg [7:0] count
  output reg [0:0] sat

  rule tick :=
    if (count == 255) sat <= 1;
    else count <= count + 1;

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

## Semantic boundary

The authoring layer obeys one rule:

> Every hardware token corresponds to one unambiguous core constructor. A
> token that would require choosing among plausible semantics is omitted until
> the core represents that choice explicitly.

In particular:

1. Every construct lowers to the existing core. No new expression, action, or
   transition semantics lives only in the parser or elaborator.
2. Assignment is nonblocking `Act.write`; there is no blocking `=` statement.
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
   compilation obligations and must not be hidden merely to resemble Verilog.
9. Command-time checks improve locations and messages but never replace core
   validation or the fail-closed emission gate. Programmatically constructed
   designs retain the same authoritative checks.

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
- concatenation;
- zero- and sign-extension, using syntax that makes the target width explicit;
- memory reads;
- parentheses;
- `$(term)` for an ordinary Lean term expected to elaborate as `Expr w`.

The initial `hwstmt` forms are:

```lean
r <= expr;
mem[port n, addr] <= expr;
if (cond) statement
if (cond) statement else statement
begin statement* end
$stmt(term);
```

`$stmt(term);` expects `Act`. It is deliberately distinct from `$(term)`,
which expects `Expr w`; expression and statement escapes never blur.

Purely structural forms lower with macros:

```text
expression operator  -> the corresponding Expr constructor
if                    -> Act.ite
begin/end sequence    -> right-associated Act.seq ending in Act.skip
```

Assignments and escapes use term elaborators rather than translation macros.
The assignment elaborator first elaborates the target, obtains `w` from its
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
input wire [hi:0] name
output reg [hi:0] name
output reg [hi:0] name := reset-value
reg [hi:0] name
reg [hi:0] name := reset-value
```

Only `[N:0]` is accepted initially. The low-bound token receives a targeted
error for any other value. `input reg` and `output wire` are not accepted:
the former lies about writability, while combinational outputs require their
own core `CombOutput`-shaped production rather than pretending they are state.
An initializer is declaration syntax, not `hwexpr`: it elaborates with expected
type `BitVec width` and becomes the `RegDecl.init` value. Numeric literals use
that expected width; a computed reset image uses an explicit Lean escape. This
keeps reset values separate from expressions over pre-cycle state.

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

hardware lnp64mini where
  input wire [0:0]  m_done
  input wire [63:0] m_rdata
  input wire [0:0]  m_busy
  input wire [0:0]  cmd_valid
  input wire [6:0]  cmd_idx
  input wire [31:0] cmd_data
  input wire [0:0]  hold

  output reg [4:0]  cur
  output reg [63:0] pc := $(BitVec.ofNat 64 TEXT_BASE)
  output reg [31:0] retire
  output reg [4:0]  st

  output reg [0:0]  dmem_we
  output reg [8:0]  dmem_a
  output reg [63:0] dmem_wd
  output reg [63:0] dmem_rd

  output reg [0:0]  core_rd
  output reg [0:0]  core_wr
  output reg [31:0] core_addr
  output reg [63:0] core_wdata

  output reg [0:0]  gp_rd
  output reg [0:0]  gp_wr
  output reg [0:0]  lr_req
  output reg [0:0]  sc_req

  output reg [3:0]  trace_wp
  output reg [3:0]  trace_sel
  output reg [0:0]  trace_hit
  output reg [63:0] trace_in_pc
  output reg [63:0] trace_in_wb
  output reg [63:0] trace_rd_pc
  output reg [63:0] trace_rd_wb

  output reg [31:0] quantum
  output reg [31:0] qctr
  output reg [7:0]  cur_dom

  sync memory [63:0] dmem [0:511]
  sync memory [63:0] rf [0:1023]
  sync memory [7:0]  uart_mem [0:255]
  memory [63:0] trace_pc [0:15]
  memory [63:0] trace_wb [0:15]
  memory [7:0]  tdom [0:31]

  rule latches :=
    begin
      if (dmem_we)
        dmem[port 0, dmem_a] <= dmem_wd;

      dmem_rd     <= dmem[dmem_a];
      trace_rd_pc <= trace_pc[trace_sel];
      trace_rd_wb <= trace_wb[trace_sel];
    end

  rule trace_ring :=
    if (trace_hit)
      begin
        trace_pc[port 0, trace_wp] <= trace_in_pc;
        trace_wb[port 0, trace_wp] <= trace_in_wb;
        trace_wp <= trace_wp + 1;
      end

  rule pulse_defaults :=
    begin
      dmem_we   <= 0;
      core_rd   <= 0;
      core_wr   <= 0;
      gp_rd     <= 0;
      gp_wr     <= 0;
      lr_req    <= 0;
      sc_req    <= 0;
      trace_hit <= 0;
    end

  rule quantum_tick :=
    if (cmd_valid & (cmd_idx == $(CMD_QUANTUM : Expr 7)))
      qctr <= cmd_data;
    else if (cmd_valid & (cmd_idx == 13) & (cmd_data[0:0] == 1))
      qctr <= quantum;
    else if ($(preemptAtF0))
      qctr <= quantum;
    else if ($(qTick))
      qctr <= qctr - 1;

  rule observe_domain :=
    cur_dom <= $(tdomRd cur);

end Machines.Lnp64mini
```

An FSM arm should become recognizable hardware instead of a constructor tree:

```lean
rule fetch_boundary :=
  if (st == $(S_F0 : Expr 5))
    if (bus_req)
      st <= $(S_PAUSE);
    else if ($(curPoisoned))
      running <= 0;
    else if ($(preemptFire))
      begin
        cur <= next_ready;
        pc <= tpc[next_ready];
      end
    else if ($(sentinelPc))
      st <= $(S_GRET);
    else
      begin
        ic_tag_q  <= ic_tag[ic_idx];
        ic_data_q <= ic_data[ic_idx];
        st <= $(S_IC);
      end
```

Parametric hardware remains Lean and crosses the boundary explicitly. For
example, LNP64mini's generated per-thread wake action may remain:

```lean
def wakeAllApply : Act :=
  (List.finRange NT).foldr
    (fun i rest =>
      Act.seq
        (.ite (.and wakeEn (.eq (tstateRegs.rd i) (L2 3)))
          (tstateRegs.set i (L2 1)) .skip)
        rest)
    Act.skip
```

and the pretty rule simply uses:

```lean
rule wake_threads :=
  $stmt(wakeAllApply);
```

Balanced trees, `Fin`-generated banks, priority encoders, and reusable action
builders therefore stay ordinary Lean. Scalar state machines, conditions,
memory traffic, and assignments use the hardware notation. Both paths produce
the same `Act` values.

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
sync memory [63:0] rf [0:1023]
memory [63:0] trace_pc [0:15]
output reg [31:0] tlb_base [8]
```

The final productions must determine without ambiguity:

- memory address width and data width;
- logical depth and whether non-power-of-two depth is permitted;
- reset image expressions;
- `syncRead` policy;
- `ackInit` policy;
- `RegArray` versus `Mem` lowering;
- exported versus internal register families;
- the generated Lean handle names and physical signal base names;
- explicit write-port indices at every memory write.

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
3. Freeze examples for the tutorial, dangling `else`, nested `begin` blocks,
   expression precedence, explicit memory ports, and both escape categories.
4. Decide ASCII spellings for signed/unsigned comparison and bitwise operators
   before any public parser surface ships.

### Phase 1: wrappers and scalar expression/statement syntax

1. Add a syntax module that imports only the existing authoring core.
2. Declare `hwexpr` and `hwstmt` plus `[hwexpr| ...]` and `[hwstmt| ...]`.
3. Implement pure constructor lowering with macros.
4. Implement assignment and escape elaborators with expected-type propagation.
5. Add `Input`, `Input.rd`, its coercion, and `addWireInput` additively.
6. Test that an input cannot reach `Reg.set` even when the friendly diagnostic
   is bypassed.

### Phase 2: scalar `hardware` command

1. Parse declaration-first scalar inputs and registers followed by rules.
2. Generate handles and rule definitions in the current namespace.
3. Accumulate `Declarations` and emit `Design.ofDecls` using the command token
   only as the design's string name.
4. Elaborate optional register initializers against expected `BitVec w` and
   preserve their values in `RegDecl.init`.
5. Preserve source locations with `withRef` and declaration ranges.
6. Implement collision checks across user names, generated names, reserved
   suffixes, and the current environment.
7. Generate public `_name` lemmas and reserve their names.
8. Add `Loom.Hw.Dsl` as the opt-in aggregate. Existing imports see no syntax or
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

- dangling `else`, asserting nearest-`if` association;
- sequencing and empty/nested `begin` blocks;
- every precedence boundary;
- writes to inputs;
- target/RHS and splice width mismatches;
- register reset-value width mismatches;
- nonzero slice lows and dynamic slice attempts;
- duplicate registers, inputs, rules, and cross-category names;
- collisions with `design`, `declarations`, generated suffixes, and an existing
  Lean declaration;
- declarations after the first rule;
- unsupported or ambiguous operator spellings.

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
5. Test multiple write sites, port ordering, sync-read obligations, reset
   images, non-power-of-two depths, and policy diagnostics.

### Phase 7: staged LNP64mini conversion

Convert by coherent blocks rather than rewriting `Core.lean` at once:

1. ports, scalar handles, and direct read aliases;
2. pulse defaults and observation-only rules;
3. trace ring and registered memory-read rules;
4. cache latch/fill rules and explicit memory ports;
5. small FSM arms;
6. command handling and larger dispatch trees;
7. register families, thread tables, and TLB structures;
8. remaining rules and declaration assembly.

After every block, require equality of the lowered `Design` or an equivalent
structural characterization, the existing `DesignWF` and sync-read checks,
FastEval/DagEval agreement, deterministic emitted RTL, and the current
LNP64mini behavioral and board-facing regression suite. Generated Verilog
should remain byte-identical whenever only authoring syntax changed; any
difference stops the migration for review.

Do not mechanically force balanced priority trees, large `List.finRange`
builders, or reusable parametric actions into statement syntax. Keep those as
Lean definitions and splice them. The success criterion is readable hardware,
not eliminating Lean from a Lean EDSL.

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
