# Post-synthesis equivalence checker

The equivalence flow compares an emitted µVerilog module with a local Yosys
`write_json` netlist. It checks one-cycle transition and output cones and
requires every UNSAT result to carry an LRAT proof accepted by
`Loom.Dp.Cert.checkLrat`.

Run it through:

```sh
scripts/eqcheck.sh rtl/<module>.v
```

The lower-level executable accepts:

```text
lake exe eqcheck [--ack name,name] <module.v> <netlist.json>
```

## Comparison

Side A is parsed from the emitted text, not reused from an in-memory
`Design`. Side B is built from the supported Yosys cells and net connections.
Registers, inputs, reset behavior, and architectural outputs are matched by
name and width. Unknown cells, combinational loops, unmatched required state,
and unsupported primitive shapes fail closed unless the tool prints a
specific exclusion admitted by policy.

Supported cell semantics include the LUT, flip-flop, carry, mux, constant,
and wiring primitives emitted by the repository's XC7 flow. This is not a
general Verilog or arbitrary-netlist equivalence checker.

## Memories

`Loom/Netlist/Mem.lean` recognizes supported distributed- and block-memory
shapes. The checker compares initialization images and delivery constraints,
write clock/enable/address/data cones, and read addresses and latency shape.
Read data is cut consistently while the recognized bank structure provides
the additional memory evidence.

The checker reports remaining boundaries individually, including arrays
removed as unobservable, fabric-resident storage, multiple source write ports
sharing one bank, and unsupported split read-data shapes. The standalone
memory-initialization script remains an independent cross-check.

## Encoder coverage

The µVerilog expression encoder is proved for literals, references, Boolean
operators, add/subtract, equality, unsigned comparison, mux, slice, and
zero/sign extension. Variable shifts and signed less-than remain outside that
proved fragment. The verdict states whether the design used any such
operator.

The netlist cone encoder is unproved. So are JSON interpretation and matching
policy, Yosys, CaDiCaL, and process/file plumbing. `TRUST.md` and `TCB.md`
state the resulting trust boundary precisely. LRAT checking validates solver
witnesses; it does not prove those upstream encoders correct.

## Verdicts

Each item is printed as `PASS`, `FAIL`, `SKIP`, or policy `ACK`. The summary
includes checked, excluded, and acknowledged counts, clause totals, LRAT
status, and encoder coverage. An `EQCHECK OK` line therefore means exactly
the checks and exclusions printed above it; it is not whole-board or physical
equivalence.

Regression coverage must include a mutated-netlist negative control, the
lost-memory-initialization fixture, unsupported-cell failure, and current
supported artifacts. Acknowledgements are explicit command-line policy and
must never be confused with checked signals.
