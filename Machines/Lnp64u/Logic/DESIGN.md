# L1 — µLog: design

**Named win (Rule 5):** the resource algebra *is* T9's conserved-quantity accounting —
memory ranges, cap slots, lineage cells, budget time — the same terms from
`Machines/Lnp64u/Types.lean`/`Cap.lean`, so the logic and the conservation theorem cannot
drift. Cerise/Iris give the blueprint (papers only, Rule 4); µLog is scoped to exactly this
machine.

## Phase 1 (gates everything): plain invariants — `Invariant/`

No separation logic at all. Inductive invariants over `machine m : TSys` via
`TSys.Inductive` + product constructions. Target order (matching PLAN §8):

1. **WF invariant** (the workhorse): slot generations ≥ 1 and ≤ retired; live entries'
   lineage indices point at occupied cells; cells' parents are live refs; regions' backings
   live or swept next revoke; activation records consistent with `serving`/`blocked`;
   Mover refs owned by owner. Everything else strengthens this product.
2. **T9**: exact accounting — occupied slots/cells/budget as a conserved ledger over
   `step`'s phases.
3. **T2**: authority of every reachable state ⊆ manifest closure under
   dup-narrow/grant-subrange/gate-transfer/drop/revoke. The closure is defined over
   `CapKind` ordering (`Perms.le`, range inclusion) + the lineage graph.
4. **T8, T4, T3, T6, T5, T7** per PLAN.

## Phase 3: the step-indexed logical relation — `Sep/`, `LogRel`

- BI algebra over the resource monoid above (`Loom/Logic` holds the generic BI/step-index
  core; everything mentioning µ nouns lives here).
- Later modality + Löb induction; the unary logical relation "safe-to-execute under
  authority A" defined directly over the µ spec, giving T2′/T4′ with adversarial
  quantification (unknown code holding capabilities to code).
- Nothing in Phases 1–2 depends on this landing (charter's honest budget).

## Staffing note (charter §8)

This is the hardest in-house component; the Iris/Cerise literature is the complete
blueprint. The invariant mainline above is deliberately independent of it.
