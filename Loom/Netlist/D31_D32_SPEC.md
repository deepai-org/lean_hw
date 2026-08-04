# Memory and encoder coverage in equivalence checking

This note records the current boundary of the post-synthesis checker. The
complete checker interface and verdict semantics are in `EQCHECK_SPEC.md`.

## D31: memories

The checker recognizes supported Xilinx memory cells and compares their
initialization parameters, write-port cones, read-address cones, and declared
synchronous or asynchronous read shape. Read data is cut consistently rather
than represented as an unbounded array-state equivalence proof. Unknown
memory cell types are errors. The regression
fixture for the lost initialization-image defect ensures that an all-zero
netlist image cannot silently match a nonzero source image.

The standalone memory-image check remains useful as an independent
cross-check, but it is not a substitute for equivalence. Any memory boundary
that remains outside the miter must be named in the verdict with its reason;
an aggregate exclusion count is not sufficient evidence.

## D32: encoder

The Lean development proves the supported Boolean/CNF encoder fragment used
by the checker. The fast executable path remains connected with
`implemented_by` and is therefore explicitly audited. Operators outside the
proved fragment, external netlist parsing and normalization, the SAT solver,
and LRAT production/checking retain the trust status stated in `TRUST.md` and
`TCB.md`.

A successful verdict must distinguish proved encoder coverage from any
unverified routing. It must never summarize a partially covered operator set
as fully verified.

## Required regression evidence

- the lost-memory-initialization fixture fails;
- supported current artifacts pass;
- unknown cells and unsupported operators fail closed; and
- the emitted verdict enumerates all exclusions and the encoder fragment in
  force.

These are current acceptance conditions, not a claim that arbitrary Yosys
netlists or memory technologies are supported.
