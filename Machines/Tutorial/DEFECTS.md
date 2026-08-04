# Tutorial-path issues

This file tracks current friction in `TUTORIAL.md`. Resolved run logs and
maintainer history are intentionally omitted.

## Open issues

- Cycle proofs over literal rule lists still depend on a documented `simp`
  recipe. A focused `cycle_simp` tactic or library simp set would make the
  first proof less sensitive to user definition names.
- `lake env lean --run` requires a root-level `main`; Lean's error for a
  namespaced entry point is not especially instructive. The tutorial states
  the requirement.
- Intermediate proof attempts can trigger linter noise before the proof is
  stable. This is harmless but distracting for first-time users.

The shipped tutorial path otherwise includes generic `Design.emit`, simple
init/step unfolding lemmas, explicit outputs, compilation, invariant
transport, and artifact emission.

## Acceptance protocol

A fresh executor should be able to complete `TUTORIAL.md` from a clean
checkout without reading library source. Record only unresolved excursions:
the command or proof that failed, the undocumented fact needed to continue,
and the smallest documentation or API change that removes it. Do not retain
dated transcripts once the issue is fixed.
