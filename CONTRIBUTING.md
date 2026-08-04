# Contributing

Contributions are welcome. Two ground rules, both chosen for trust in both
directions:

## Licensing of contributions

By contributing you agree your contribution is licensed under the
repository's licenses: Apache-2.0, plus Solderpad SHL-2.1 for anything
under `Machines/` (see `LICENSE`, `Machines/LICENSE`, `NOTICE`). There is
**no CLA** and there will not be one — you keep your copyright; the
project never acquires the power to relicense your work out from under
you.

## Developer Certificate of Origin (DCO)

Instead of a CLA we use the [Developer Certificate of Origin
v1.1](https://developercertificate.org/): a one-line assertion that you
have the right to submit the code under the project license. Sign off
every commit:

    git commit -s

which appends `Signed-off-by: Your Name <you@example.com>`. That line is
the entire process.

## The audit gate

Every contribution must keep the package, test, and trust gates green:

```console
scripts/quality.sh
lake build
lake test
lake exe audit
```

Run `scripts/ci.sh` when the change reaches emitted artifacts or the broader
tool workflow. The audit permits `sorry` only in the explicitly reported
theorem/WIP policy, bans `native_decide` on theorem paths, and allows only the
two named µVerilog boundary declarations plus the standard Lean axioms. It
also inventories unsafe code and executable replacements.

Theorem statements are contracts. Weakening one requires an explicit claim
review; producing a counterexample to a false statement is a valuable
contribution and should lead to a visible repair of the statement or design.
