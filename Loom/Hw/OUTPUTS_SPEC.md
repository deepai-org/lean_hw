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
