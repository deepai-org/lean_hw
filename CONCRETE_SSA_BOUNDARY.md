# Concrete SSA to Yosys semantic boundary

This document states the one non-kernel semantic adequacy assumption between
the exact certified Verilog bytes and Yosys. It is deliberately about the tiny
release language in `Loom/Release/SSA.lean`, not arbitrary Verilog.

The release theorem proves `Symbolic.ModuleBehavior design program ...` and
exact bytes for `program.renderTree`. `SSA.Program.elaborate` gives the
corresponding executable elaboration into Loom's intrinsically typed
µVerilog AST; the production certificate uses the more scalable direct
`ModuleBehavior` relation, whose obligations cover the same wires, registers,
memories, ports, and outputs without trusting execution of the elaborator.

## Assumption

For any accepted release `program`, when Yosys reads exactly the bytes of
`program.renderTree.flattenBytes`, its two-state synchronous transition
behavior is the behavior assigned by `Symbolic.ModuleBehavior` and the Loom
µVerilog module semantics:

- the modeled initial/reset state contains exactly the declared register reset
  values and complete memory initialization image;
- a cycle reads the pre-edge state, evaluates the named acyclic SSA graph,
  and commits register and enabled memory writes on the positive clock edge;
- nonblocking assignments commit together, with later source-ordered writes
  to the same memory location taking precedence; and
- continuous outputs expose the named values at their declared widths.

This is an explicit adequacy assumption, not a Lean axiom used by
`verifiedReleases`. The Lean theorem ends at exact bytes plus the formal
denotation; Yosys is trusted when interpreting those bytes as hardware.

## Entire admitted expression language

Every wire is a single explicitly sized SSA assignment. Operands name a source
register or an earlier wire and are width-checked by the accepted denotation.

| Concrete constructor | Rendered Verilog | Formal meaning |
|---|---|---|
| `lit w n` | `w'dn` | low `w` bits of `n` |
| `ident x` | `x` | width-checked identity/zero extension |
| `memRead m a` | `m[a]` | asynchronous read at address `a` |
| `slice x hi lo` | `x[hi:lo]` | inclusive bit slice |
| `not x` | `~x` | bitwise complement |
| `and/or/xor` | `x &/|/^ y` | same-width bitwise operation |
| `add/sub` | `x +/- y` | same-width modular arithmetic |
| `shl/shr` | `x <</>> y` | same-width logical shift result |
| `eq/ult` | `x == y`, `x < y` | one-bit equality/unsigned comparison |
| `slt` | `$signed(x) < $signed(y)` | one-bit two's-complement comparison |
| `mux c t f` | `c ? t : f` | one-bit condition, same-width arms |
| `sext k x s` | `{{k{x[s]}}, x}` | sign extension from the top input bit |

No procedural combinational blocks, latches, delays, event controls other than
the single positive-edge block, blocking sequential assignments, `x`/`z`
literals, casex/casez, tri-states, force/release, DPI, `$random`, unsized
literals, generate statements, or user-defined Verilog functions occur in the
release subset.

## Module framing

`Program.renderTree` emits, in fixed order:

1. one module header with `clk`, `rst`, and explicitly sized outputs;
2. explicitly sized register and memory declarations;
3. one complete `initial` image per memory;
4. the ordered SSA wire declarations;
5. one `always @(posedge clk)` block containing synchronous reset, register
   next-state assignments, and ordered guarded memory writes;
6. continuous output assignments; and
7. `endmodule`.

The renderer preserves this structure as bounded LF-oriented rope leaves.
Lean proves the leaf equalities and balanced composition; the external binding
step validates the actual theorem rope order and uses exact `cmp` against the
host file.

## Conditions and exclusions

- The formal values are two-state `BitVec`s. Four-state simulation behavior is
  not modeled. The release gate separately rejects X/Z/don't-care syntax,
  missing register resets, and incomplete memory images.
- Reset is synchronous and begins from the modeled reset contract. Electrical
  reset sequencing, metastability, clock startup, scan state, and retained
  SRAM are outside this assumption.
- Memory inference must preserve the stated asynchronous-read,
  synchronous-write behavior and source-order collision policy. Target RAM
  primitives or synthesis options that change that behavior are outside it.
- Timing, placement, routing, CDC behavior, glitches, power, analog effects,
  and unmodeled SoC agents are downstream assumptions, not consequences of
  `ModuleBehavior`.

The final acceptance environment uses Yosys 0.33
(`2584903a060`) and Icarus Verilog 12.0 for corroborating synthesis/simulation.
Those tests are evidence for this boundary, not substitutes for the stated
trust assumption. A deployment must record the Yosys version and relevant
synthesis options it actually trusts.
