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

Every contribution must keep `lake exe audit` green: `sorry` only under
`Machines/*/Theorems/` and `Wip` namespaces, no `native_decide`, no new
axioms (the single `ImplementsStandard` axiom is whitelisted).
`scripts/ci.sh` is the full check. Theorem statements are contracts — a
PR that weakens a statement to make it provable will be declined; a PR
that *refutes* a statement with a counterexample is a prized
contribution (see the proof-forced findings in `STATUS.md` for the house
style of recording them).
