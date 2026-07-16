## Summary

Describe the user-visible or proof-visible change and why it is needed.

## Verification

- [ ] `bash scripts/quality.sh`
- [ ] Relevant focused Lean targets
- [ ] `lake exe audit`
- [ ] `bash scripts/ci.sh` when practical
- [ ] Commits carry a DCO `Signed-off-by` line

## Trust and compatibility

- [ ] I identified any change to axioms, sorries, unsafe/partial/extern code,
      `implemented_by`, the audit whitelist, or emitted-artifact assumptions.
- [ ] I identified any weakened or materially changed theorem statement.
- [ ] I updated status/trust documentation when a public claim changed.
- [ ] I noted any Lean-version, package API, RTL, or downstream compatibility impact.
