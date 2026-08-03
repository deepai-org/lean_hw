# D39 — declared observability (`Design.outputs`)

Discovered by the capability engine: **Loom cannot keep a secret.** Every
register in a `Design` is emitted as an `o_<name>` output port, so the MAC key
in `Machines/CapWalk/Engine.lean` had to become a bitstream constant rather
than a register — recorded as deviation CE5, with the note that "a
never-written register would emit as an `o_*` port and publish the key". For a
machine whose premise is capability enforcement, an EDSL that structurally
cannot hold a secret is a defect, not an inconvenience. Secondary cost: port
lists are unconditional, so `lnp64mini_epoch` carries ~450 ports.

## The decision (chosen over a per-register `observable` flag)

Observability is a property of the design's **interface**, so it is declared
once at the design:

    structure Design where
      …
      /-- D39: which registers this design exports. `none` = every register
      (today's behaviour, so existing designs emit byte-identically);
      `some ns` = exactly the named registers. A register absent from the
      selection is INTERNAL: it appears in the module body but at no port. -/
      outputs : Option (List String) := none

Rationale for the design-level selection over a `RegDecl` field: it composes
with D16 (a `par`/`connect` may rewrite what the composite exports without
touching any register declaration); it mirrors µVerilog's existing
`Module.outs`; and it survives `Fin n`-generated register lists, where a
per-declaration flag would have to be threaded through every builder.

## What must be true

1. **Default is identity.** `outputs = none` reproduces today's
   `outs := d.regs.map …` exactly. Every currently-emitted `rtl/*.v` must be
   byte-identical after this lands — that is the acceptance test, and it is
   what makes the change safe under silicon-proven artifacts.
2. **Well-formedness.** A name in `outputs` that is not a declared register is
   an error at `Design.emit` (same place as the D15 name-clash and D37 image
   checks), naming it.
3. **The theorem worth having** — state and prove it, do not merely arrange
   it: for a design with `outputs = some ns`, no register outside `ns` appears
   in `(compile d).outs`. That is the architectural non-export property, and it
   is what lets a key live in a register.
4. **Composition.** `prefixed` renames selections with the registers.
   `par` concatenates. `connect` must not resurrect a dropped output. State
   what each does; prove what is cheap.

## Honesty boundary (state this in the docs, do not let it drift)

Declared observability prevents **architectural** disclosure: the value is at
no module port, so nothing above the design boundary can read it. It does NOT
prevent physical extraction — a bitstream can be read back on most FPGAs, and
a constant or a reset value is recoverable from it. The claim is "not exported
at the interface", never "unrecoverable from the device"; a threat model that
needs the latter wants key derivation from a device secret, which is out of
scope here and should be named as such.

## Payoffs beyond the key

* `Machines/CapWalk/Engine.lean` CE5 can retire: the MAC key becomes an
  ordinary register, so per-boot or per-domain re-keying becomes expressible.
* Port lists collapse to what is actually observed, which helps synthesis and
  makes the board wrappers legible (~450 ports on `lnp64mini_epoch` today).
* The eqcheck output-port leg gets smaller and more meaningful: it checks the
  exports a design *intends*, not every register it happens to have.

## Status: SHIPPED 2026-08-01

`Loom/Hw/Syntax.lean` (`Design.outputs`, `Design.exportedRegs`),
`Loom/Hw/Compile.lean` (both `compile` and its `implemented_by` twin read
`exportedRegs`), `Loom/Hw/Outputs.lean` (the check, the theorem, the
composition lemmas), `Loom/Hw/EmitIO.lean` (the refusal),
`Loom/Hw/Compose.lean` (§4), `Tests/Outputs.lean`, ledger entry
`LOOM_GAPS.md` D39.

What was proved, in the three levels §3 asked for:

* `compile_not_exported` — for `outputs = some ns`, a name outside `ns` is
  neither the name of an output port of `compile d` nor read by any output
  port's driver expression. Stated for an arbitrary name, not merely a
  declared register.
* `compile_portNames_not_exported` — the same over the module's whole port
  list (D15 inputs included), given that no input is named `o_<n>`.
* `printed_not_exported` — **the stronger statement §3 invited**: over the
  emitted *text*. Given the artifact's round-trip verdict
  (`Module.parseCheck`, which `lake exe rtlroundtrip` runs over every
  `rtl/*.v` in CI), the module recovered from the file by the independent
  parser exports no unselected name either.

Composition, per §4: `prefixed_exportedRegs` (the selection renames with the
registers), `par_exportedRegs` (concatenation, under the disjointness
`parOkB` already provides) with `par_exportedNames_subset` as the
hypothesis-free safety half (`par` cannot publish what neither part
exported), and `connect_exportedRegs` (wiring cannot resurrect a dropped
output; `rfl`).

The artifact: `Machines/CapWalk/Engine.lean`'s MAC key is now six ordinary
registers held off the interface, and deviation CE5 is retired. The board
artifacts were deliberately **not** re-cut with selections — `rtl/*.v` other
than the two capability-engine files are byte-identical, which was the
acceptance test.

**Correction to the "payoffs" section above, from measurement.** "Port lists
collapse, which helps synthesis" is not demonstrated. Emitting
`lnp64mini_epoch` with a selection equal to the 76 ports its ZC702 wrapper
reads (down from 427) drops `OBUF` 9820 → 1121 and leaves the flop count
alone, but *raises* total cells 52979 → 63456 under `synth_xilinx -flatten
-nowidelut` on a standalone top, because the de-ported cones re-optimize
differently. Likewise, `capwalk` synthesizes to a byte-identical cell census
before and after the key became six unexported registers — yosys folds a
never-written register back into the constants it came from. Declared
observability is an **architectural** statement; any resource claim about it
must be measured in the wrapper the design is instantiated in.
`LOOM_GAPS.md` D39 carries the table.


## D39a — `outputs` is mandatory (2026-08-03)

`outputs` was `Option (List String)` defaulting to `none` = "export every
register". That was a mistake, and the operator called it: **the default was
maximal disclosure**, so D39's protection applied only to designs that opted
in. It is the same shape as the `checkD19` helper each machine used to call
by hand before D19 moved into `Design.emit` — *protection a caller can forget
is not protection*. Inputs have always been explicit; outputs are the other
half of the interface and are explicit now.

The field is `List String` with no default. A design whose whole register set
genuinely is its interface says so — `outputs := regs.map (·.name)`, or a
literal name list. `exportedRegs` is a plain filter; the `none` identity
theorems are replaced by `exportedRegs_all`, which states the same thing for
a design that names everything, and `Design.par` concatenates its parts'
selections with no case analysis left.

**Acceptance (run 2026-08-03).** Every design in the repo declares `outputs`;
re-emitting the shipped RTL leaves **12 of 17 files byte-identical**. The five
that differ are accounted for and none is an observability change: the
lnp64mini family gained `o_quantum`/`o_qctr`/`o_cur_dom`/`o_wake_key` from
EXT-1/EXT-2/EXT-4 (their baselines predate those increments), and `capwalk.v`
has an **identical output-port set** — its diff is an unrelated earlier edit.
