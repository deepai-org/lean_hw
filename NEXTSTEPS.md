# Next steps

This is the active, ordered work queue. It contains only current work; Git and
the changelog preserve completed campaigns. Strategy beyond the immediate
queue is in [`PLATONIC.md`](PLATONIC.md).

## P0 — restore a releasable head

1. **Restore repository gates.** Update stale test designs for mandatory
   `Design.outputs` and the current output API, and add the two missing
   PingPong SPDX headers.
2. **Re-run the complete local gate sequence:**

   ```console
   scripts/quality.sh
   lake build
   lake test
   lake exe audit
   scripts/ci.sh
   ```

3. **Resolve the LNP64mini board regression.** The console-ring symptom points
   at byte stores, while the new compiled subword test passes both modeled
   memory paths. Force a fresh `minitest`/emission/RTL/bitstream build, repeat
   the board trace, and then isolate any remaining wrapper or synthesized-path
   difference. Re-run the complete emulator, RTL, and silicon ladders.
4. **Rebuild the release from clean state.** Run Tier A only after the source,
   test, and quality gates are green; retain its metrics and exact tool
   versions with the release record.

## P1 — finish single-source interfaces

- Introduce typed register and memory handles so widths and names are declared
  once.
- Add declaration/notation support that elaborates to the existing `Design`
  representation.
- Generate complete state comparators from declarations. Any omitted state
  must be an explicit, named exclusion; a lockstep test must not pass because
  someone forgot to compare new state.
- Migrate LNP64mini without unexplained RTL drift and update the tutorial to
  the public interface.

Acceptance: misspelled reads/writes fail at emission, comparator completeness
is generated, and the migrated design has an enumerated zero-or-intended RTL
diff.

## P2 — make proofs scale with touched state

- Prove generic frame lemmas from action footprints.
- Infer supports for common invariants and discharge disjointness checks
  mechanically.
- Provide a stable `cycle_simp`/rule tactic so user proofs do not unfold an
  entire large design by hand.
- Demonstrate the method on a real LNP64mini invariant and on the tutorial
  examples, with measured proof size and check time.

Acceptance: proof effort is proportional to rules that touch the property,
not to the full register/rule count.

## P3 — grow verified transformations

The balanced tree builders and their evaluation theorems are in `Loom/Hw`.
Next:

- generalize `retimeReg` to selected feed-forward cuts and multiple stages;
- add fan-out duplication with a proved coherence invariant;
- compose `Simulation` and `StutterSimulation` chains; and
- transport invariants through a transformation chain in one step.

Acceptance: one nontrivial timing change is emitted and measured while its
model property is transported by the generic transformation theorem.

## P4 — strengthen synthesis validation

- Run the large SoC equivalence checks in the standing/manual gate and retain
  complete exclusion reports.
- Minimize acknowledged memory-bank defects and unsupported operators.
- Add a second target cell-library instance without changing the generic
  miter/encoder/checker core.
- Keep the independent memory-image checker as a cross-check.

Acceptance: every shipped RTL artifact is either checked or explicitly marked
outside the supported fragment by the release evidence.

## P5 — derive fast executable views

Generate a specialized cycle evaluator and complete comparator from a
`Design`, with a kernel-checked equality to `Design.cycleOpen`. Migrate
LNP64mini away from its hand-maintained mirror only after the generated path
is within twice the compiled hand evaluator's runtime.

## P6 — target-parameterized cost models

Add target-independent expression depth, DAG area, and duplication reports,
then calibrate target profiles against post-route evidence. Predictions must
carry error bars and must not be presented as timing or fit theorems.

## Release/community follow-through

- Define and document the supported Lean-version window and upgrade canary.
- Publish generated API documentation for the intended public surface.
- Resolve the package/module naming decision before the first stable tag.
- Establish public API/docstring linting and split CI reporting by proof,
  package, RTL, and optional external-tool scope.
