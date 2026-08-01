# Release theorem and trusted computing base

## The single theorem

The publication-facing declaration is:

```lean
theorem Loom.Release.Theorems.verifiedReleases :
  Nonempty Loom.Release.Theorems.VerifiedReleases
```

Its structure contains fixed Acc8 and LNP64-µ artifacts. For each artifact,
the Lean kernel checks:

- exact equality between the concrete SSA renderer's byte rope and the
  theorem-bound disk byte rope;
- complete declarative denotation of that concrete SSA program as the
  reference `Compile.compile` output, including metadata, every indexed wire,
  register next-state fold, memory initialization/write port, and output;
- a simulation from the fully proved processor model to that compiled
  transition system; and
- transport of every model invariant to every reachable compiled state.

The combined theorem names four security consequences over the exact LNP64-µ
compiled system: authority confinement, machine-wide W^X, lineage-ledger
conservation, and budget boundedness. Its proof is assembled from the Acc8
A-R/AEV chain and the LNP64-µ R-MC/compiler-simulation chain; a reader does not
need to compose those internal lemmas mentally.

`Tools/ReleaseAudit.lean` rejects the release unless the axiom closure of this
one declaration is exactly:

```text
propext
Classical.choice
Quot.sound
```

## The complete trusted list

To claim the theorem about the two host files and then interpret those files
as synthesized hardware, trust is limited to:

1. **Lean's kernel and the three axioms above.** The kernel accepts every
   generated leaf, balanced composition node, artifact theorem, and the final
   combined theorem.
2. **One exact file-binding step.** The generated release source embeds disk
   literals split at LF boundaries. Large line sequences use 128-item leaves;
   the generator groups four leaves per source batch, while balanced ropes
   preserve theorem-defined order. `scripts/check_release_binding.py`
   reconstructs those literals and invokes one standard `cmp -s` against
   `rtl/acc8.v` or `rtl/lnp64u.v`. This small association step is trusted; no
   hash or collision-resistance assumption is used.
3. **The concrete-SSA/Yosys adequacy statement.** For the deliberately small
   syntax emitted by `SSA.Program.renderTree`, Yosys is assumed to assign the
   Verilog text the transition behavior specified by the proved
   `Symbolic.ModuleBehavior` relation. Its complete construct-by-construct
   statement is [`CONCRETE_SSA_BOUNDARY.md`](CONCRETE_SSA_BOUNDARY.md).
4. **The downstream physical flow**, only when extending the claim from the
   exact Verilog bytes to a netlist or physical implementation — and now a
   *smaller* item than it was. `lake exe eqcheck` checks emitted-module ≡
   post-synthesis netlist per build, registers and memories alike, every UNSAT
   LRAT-certified and re-checked by the proved checker, with the encoder's
   expression side proved (`Loom.Netlist.encode_sound`) over a named operator
   fragment. What remains trusted here: the netlist-side cone walk and cell
   library (a named hypothesis of that theorem), the three unproved operators
   `shl`/`shr`/`slt`, the excluded signals each run names, and everything
   below the synthesized netlist — placement, routing, FASM and bitstream
   generation, which are corroborated by running the artifact on hardware
   rather than proved (`LOOM_GAPS.md` D33 records why that boundary is drawn
   where it is).
5. **The single-flop resolution (MTBF) assumption**, only when extending the
   claim from the emitted single-clock core to a board wrapper that drives it
   across a clock boundary (`fpga/zc702/lnp64mini_soc_top.v`,
   `lnp64mini_dual_top.v`). Stated once: *a flop whose input changes inside
   its sampling aperture may resolve to either Boolean value, but it resolves
   to one of them before the next clock edge.* Nothing about resolution
   probability, aperture width, or timing margin is assumed, and no physics is
   verified. `Loom/Hw/CdcContract.lean` encodes exactly this assumption
   structurally — the first synchronizer flop's sample on an event cycle is
   supplied by an adversarial oracle — and proves the wrapper's toggle/2FF/XOR
   command path correct for *all* oracles; `Loom/Hw/DESIGN.md` §D21 enumerates
   the four crossings and the read-back capture classes this assumption is
   applied to. The release theorem itself does not need item 5: release
   designs are closed and single-clock.

The generated Verilog syntax is intentionally structural: one statement per
line, named width-indexed SSA wires, explicit registers and memory ports, and
fixed reset/cycle framing. Every additional construct would enlarge item 3.

## Explicitly outside the TCB

The optimized `compileImpl`/`printImpl` path, witness generator, unsafe
certificate synthesizer, generated proof-text generator, compiled evaluator,
audit reporter, simulation scripts, hashes, and cached `.olean` files are not
soundness assumptions. They propose data or report checks. A defect in them
can make the build fail or produce a rejected witness; it cannot make the Lean
kernel accept a false declaration.

The audit is a hard release gate and an important independent inventory, but
it is not substituted for kernel checking. Cached objects are only a restart
convenience and are not publication proof evidence.

The release command also runs `scripts/check_xfree_rtl.py` over the freshly
bound files. That syntactic subset check corroborates the stated Yosys
adequacy boundary; it does not replace either the kernel theorem or the
explicit semantic assumption.

## Claim boundary

The theorem is about the two-state closed processor model and the exact
Verilog core bytes. Reset electronics, X/Z behavior outside the emitted
subset, DMA, interrupts, debug, unmodeled SoC fabric, analog timing, power,
and physical side channels are not silently covered. `TRUST.md` records these
limits and the hypotheses of the security theorems; `REPRODUCING.md` explains
how an outsider independently re-derives the claim.
