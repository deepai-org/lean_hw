import Machines.Lnp64u.Logic.NonInt

/-!
# T5 — Noninterference (architectural, path-free pairs)

Donation deliberately couples timing along authority paths, so the theorem
quantifies over pairs with *no* path, and observes architectural state
modulo stuttering: an isolated domain's destuttered trajectory is a
function of its own configuration and code only. Stated as a two-manifest
(2-safety) property.

**Adjudication note (recorded in full in `Logic/NonInt.lean`).** The
original statement — `Isolated` + `AgreeOn` alone — was **false**: the
other domains' priorities and budgets were unconstrained, so the second
manifest could contain a higher-priority hog with `budgetQ = periodP`
(legal under `Manifest.WF`) that monopolizes the core forever, freezing
`d`'s destuttered trajectory at length 1 while the first manifest lets `d`
run unboundedly. Beyond scheduling, two further channels reached `d`
without any authority overlap: `mem_grant` installs capabilities into the
*target's* slot table without consent (perturbing `d`'s own later
`cap_dup` handle values, which land in registers), and `d`'s own
`mem_grant`/`move` read foreign table state / global Mover state into
`d`'s `rd`. The repaired statement therefore adds: `TopPriority` for `d`
in both manifests, and two `Isolated` clauses (`slots_full`: `d`'s slot
table boots full; `code_local`: `d`'s code contains no
`cap_drop`/`cap_revoke`/`mem_grant`/`move`).
-/

namespace Machines.Lnp64u.Theorems.T5

open Machines.Lnp64u Loom NonInt

/-- **T5.** An isolated, top-priority domain's destuttered trajectory is
independent of everything outside its own configuration and code: under
agreement, one machine's destuttered trajectory is a prefix of the other's
(run long enough).

Proof plan (see `NonInt.Coupled` for the invariant and its docstring for
the drift analysis):
1. Two-run induction maintaining `Coupled m₁ d σ₁ σ₂` at *aligned*
   instants (equal counts of `d`-retirements); `coupled_init` starts it.
2. `schedule_top` + `payer_eq_self`: at every idle cycle `d` is issued
   iff `run = .running ∧ 0 < budget`, independent of the other domains.
3. Frame: between `d`'s own issue/retire events nothing changes `d`'s
   compared fields (`slots_full` + `code_local` close the grant-in
   channel; `no_gates_in`/`no_gates_held` close gates; `roots_disjoint`
   + authority confinement (T2) close memory and Mover writes).
4. Progress: `d` is refilled to `budgetQ` every period and wins every
   idle cycle, and every in-flight instruction terminates, so run 2's
   `d`-retirement count is unbounded; pick `k` past the alignment of run
   1's first `n` cycles.
5. Destuttering erases the inter-retirement stutter (which is where the
   two runs drift), giving the prefix. -/
theorem noninterference (m₁ m₂ : Manifest) (h₁ : m₁.WF) (h₂ : m₂.WF)
    (d : DomainId) (hiso₁ : Isolated m₁ d) (hiso₂ : Isolated m₂ d)
    (hpri₁ : TopPriority m₁ d) (hpri₂ : TopPriority m₂ d)
    (hag : AgreeOn m₁ m₂ d) :
    ∀ n, ∃ k, (destutter (trajectory m₁ d n)) <+: (destutter (trajectory m₂ d k)) := by
  -- TODO(T5): assemble from the NonInt pieces per the plan above. The
  -- remaining work is the aligned-instant simulation (steps 3–4): a
  -- cycle-level case split on `step` showing `Coupled` is preserved and
  -- that `d`'s compared fields change only at `d`'s own retirements.
  sorry

end Machines.Lnp64u.Theorems.T5
