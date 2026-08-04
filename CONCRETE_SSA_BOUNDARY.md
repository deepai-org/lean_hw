# Concrete SSA to Verilog-tool semantic boundary

This page states one assumption: how the exact certified release bytes are
interpreted as Verilog. It does not describe the release proof itself (see
[`TCB.md`](TCB.md)) or claim that Yosys/P&R is verified.

## Formal side of the boundary

For a release `program`, Lean proves:

- `Symbolic.ModuleBehavior design program ...`, a declarative account of all
  program metadata, SSA wires, registers, memories, writes, and outputs; and
- exact equality between `program.renderTree.flattenBytes` and a
  theorem-bound byte rope.

`SSA.Program.elaborate` also reconstructs the intrinsically typed µVerilog
AST, but the scalable release certificate proves the direct declarative
relation rather than trusting execution of that elaborator.

## Assumption

When a conforming Verilog tool reads exactly
`program.renderTree.flattenBytes`, it assigns the text the same two-state,
synchronous transition behavior as `Symbolic.ModuleBehavior` and Loom's
µVerilog semantics:

- registers reset synchronously to their declared values;
- memory starts with the complete declared image;
- a cycle reads pre-edge register and memory state;
- acyclic, width-checked SSA expressions have their declared bit-vector
  meanings;
- register assignments and enabled memory writes commit at the positive edge;
- later source-ordered writes to the same memory location win; and
- continuous outputs expose the named values at their declared widths.

This is not a Lean axiom used by `verifiedReleases`. The Lean theorem ends at
formal denotation and exact bytes. Yosys 0.33 (`2584903a060`) is the currently
recorded corroborating implementation, not part of the kernel proof.

## Complete release expression syntax

Each expression is the right-hand side of one explicitly sized SSA wire.
Operands refer to source registers or earlier wires.

| SSA constructor | Rendered form | Formal meaning |
|---|---|---|
| `lit w n` | `w'dn` | low `w` bits of `n` |
| `ident x` | `x` | width-checked identity; assignment context supplies zero extension where applicable |
| `memRead m a` | `m[a]` | asynchronous read at address `a` |
| `slice x hi lo` | `x[hi:lo]` | inclusive slice |
| `not x` | `~x` | bitwise complement |
| `and`, `or`, `xor` | `x & y`, `x \| y`, `x ^ y` | same-width bitwise operation |
| `add`, `sub` | `x + y`, `x - y` | same-width modular arithmetic |
| `shl`, `shr` | `x << y`, `x >> y` | same-width logical shift result |
| `eq`, `ult` | `x == y`, `x < y` | one-bit equality or unsigned comparison |
| `slt` | `$signed(x) < $signed(y)` | one-bit two's-complement comparison |
| `mux c t f` | `c ? t : f` | one-bit condition and same-width arms |
| `sext k x s` | `{{k{x[s]}}, x}` | explicit sign extension |

The release language contains no procedural combinational blocks, latches,
delays, falling-edge or multi-clock event controls, blocking sequential
assignments, `x`/`z` literals, `casex`/`casez`, tri-states, force/release, DPI,
randomness, unsized literals, generate statements, or user functions.

Do not confuse this syntax list with the smaller proved fragment of the
optional post-synthesis CNF encoder. That checker currently excludes and
reports `shl`, `shr`, and `slt`; the release denotation itself includes them.

## Module framing

`Program.renderTree` emits, in order:

1. a module header with `clk`, `rst`, and explicitly sized outputs;
2. explicitly sized register and memory declarations;
3. a complete `initial` image for each memory;
4. ordered SSA wire declarations;
5. one `always @(posedge clk)` block with synchronous reset, register
   next-state assignments, and ordered guarded memory writes;
6. continuous output assignments; and
7. `endmodule`.

The exact-byte proof uses bounded LF-oriented rope leaves and balanced
composition. The separate file binder reconstructs the theorem's leaf order
and performs exact `cmp`; it does not rely on a hash.

## Conditions and exclusions

- Formal values are two-state `BitVec`s. The release gate syntactically
  rejects major X/Z/don't-care hazards, missing register resets, and incomplete
  memory images, but that linter is not a proof of all four-state tool behavior.
- Reset starts from the modeled synchronous-reset contract. Power-on,
  asynchronous reset sequencing, PLL startup, scan, and retained SRAM are
  outside it.
- A downstream memory mapping must preserve asynchronous-read,
  synchronous-write behavior, initialization, and collision order. Tool or
  target mappings that do not are outside the assumption.
- Timing, glitches, CDC physics, P&R, configuration generation, power, and
  unmodeled SoC agents are downstream.

A deployment must record the actual tool version and synthesis options it
relies on. Passing simulation or equivalence checks is valuable evidence, but
does not replace this stated adequacy assumption.
