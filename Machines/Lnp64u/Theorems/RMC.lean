import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Logic.Inflight
import Machines.Lnp64u.Logic.Hostage

/-!
# R-MC — the LNP64-µ EDSL core refines the ISS

The machine-code refinement theorem: the EDSL core (`Hw.core m`, 1 hardware
cycle = 1 spec cycle) tracks the ISS (`machine m` = `Step.step` iterated)
exactly through the abstraction function `Hw.abs` of `Hw/Enc.lean`. This is
what transports T2–T9 from the ISS onto the emitted Verilog (text side via
the parser round-trip, tool side via the single `ImplementsStandard` axiom).

## Why the statement is the *bounded lockstep*, not a plain `Simulation`

The project plan's literal form `Simulation (machine m) ((core m).toTSys)`
is **uninhabited** — with `Hw.abs` or any other abstraction function:

* `MachineState.cycle : Nat` increases strictly at every spec step, so
  `machine m` has no periodic points.
* Every forward orbit of `(core m).cycle` is eventually periodic: a cycle
  only rewrites the finitely many declared `(name, width)` register entries
  and the finite RAM, so the orbit of any `St` lives in a finite set.
* A `Simulation.square` is a functional-graph homomorphism `h` with
  `h ∘ cycle = step m ∘ h`; it would map a concrete periodic orbit to a
  spec periodic orbit. Contradiction.

Concretely, the mismatch is the 32-bit `cycle` register wrapping at
`2 ^ 32` while the spec counter keeps counting. The refinement therefore
holds *on the 32-bit horizon*, and that is what is stated here:

* `square` — one core cycle = one spec step through `Hw.abs`, under the
  hidden-state coupling `Coupled`, datapath-fit `Fits`, reachability on
  both sides, and no counter wrap this cycle. This is the per-field,
  per-opcode workhorse.
* `abs_run` (**the R-MC headline**) — for every `n < 2 ^ 32`,
  `Hw.abs ((core m).run n reset) = stepN m n m.initState`: exact
  whole-state lockstep from reset, the formal generalization of the
  2000-cycle `Tests/Lnp64uCore.lean` run.
* `invariant_transport` — every ISS invariant (T2–T9's currency) holds of
  the abstraction of every core state on the horizon. Sorry-free given
  `square`/`coupled_step` (which carry the sorries below).

Restoring the plan's literal `Simulation` type would require a spec-side
decision (D-class): make `MachineState.cycle` a `BitVec 32` (mod-`2 ^ 32`
counter), or quotient the abstract system by counter epochs. Both touch
T5–T9's refill arithmetic; not taken unilaterally here.

## Remaining work (the sorries), itemized

1. `abs_reset` — `Hw.abs (core m).reset = m.initState`: a lookup lemma for
   `Design.reset`'s `foldl` over the 633 `regDecls` (unique names ⇒ the
   declared init wins), then per-field `enc`/`dec` round trips.
2. `coupled_reset` — same machinery; `rctr = 0 = cycle % P`, kind words in
   encoder image, `run ≠ 3`.
3. `square` — the big one. Phase decomposition mirroring `Step.step`:
   a. rule-fold characterization: `(core m).cycle σ` as the four rules'
      `Act.run` composition (later writes win);
   b. refill: `refillCondE`/`drctr` vs `cycle % P` (uses `Coupled.rctr_sync`
      and the `effBudgetE` bypass for the charge path);
   c. core, in-flight arm: countdown vs `cyclesLeft - 1`; retirement
      dispatch — per-opcode circuit vs `Isa` exec semantics (25 ops; base
      ops first, mirroring Acc8 `AR.square`'s per-op `simp` pattern, then
      the system ops of `Hw/SysOps.lean`); the `cap_revoke` arm needs the
      pointer-doubling mark-engine correctness (`rv_*` registers converge
      to the spec `marks` closure in ≤ 7 of the 22 rounds) — this forces
      an `rv`-coupling clause into `Coupled` (currently absorbed by the
      concrete-reachability hypothesis `hcr`);
   d. core, idle arm: `schedOrder` fold vs `schedule`'s max-priority fold
      (uses `WF.prio_inj`), `payerE` unrolled walk vs `MachineState.payer`,
      fetch/decode/charge/latch vs the spec issue path;
   e. mover: `SysOps.moverAct`'s pre-cycle re-derivations vs
      `moverPhase ∘ corePhase` (kill sweeps, same-cycle store forwarding);
   f. tick: `cycle + 1` with no wrap (`hwrap`).
4. `coupled_step` — preservation of `Coupled`: `rctr` increment vs counter
   increment mod `P`, canonical writes (every kind word the circuits write
   is an encoder image), `run` writes ∈ {0,1,2}.

`Coupled` is expected to grow proof-forced clauses (repo pattern); `square`
and `coupled_step` also carry `hcr` (concrete reachability), so clauses
provable from reachability can be added to `Coupled` without weakening the
assembled theorems — `lockstep_coupled` threads reachability on both sides.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw

/-! ## The coupling invariant and datapath fit -/

/-- Hidden-state / canonical-encoding coupling between a core state and its
abstraction: the register file is in the image of the encoding discipline
`Hw/Enc.lean` fixes, and the hidden refill counters track the cycle
register. (The `cap_revoke` mark-engine coupling is currently supplied by
the concrete-reachability hypothesis of `square`; it becomes a clause here
when the retirement arm forces its exact statement.) -/
structure Coupled (m : Manifest) (σ : Loom.Hw.St) : Prop where
  /-- The hidden per-domain refill counter is `cycle % P` of the *register*
  counter (both wrap together below the horizon). -/
  rctr_sync : ∀ d : DomainId,
    (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP
  /-- The run state is canonically encoded (`3#2` is decode fallback only;
  the circuits test `= 0`, the spec tests `.running`). -/
  run_canon : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2
  /-- Every live capability's kind word is in the encoder image (`decKind`
  drops the unused high bits, which the circuits copy verbatim). -/
  kind_canon : ∀ (d : DomainId) (s : Slot), σ.regs (Hw.dcapV d s) 1 = 1#1 →
    Hw.encKind (Hw.decKind (σ.regs (Hw.dcapKind d s) 32)) =
      σ.regs (Hw.dcapKind d s) 32

/-- The manifest's `Nat` scheduling parameters fit the 32-bit datapath
registers that carry them (`budgetQ < 2 ^ 32` follows via `WF.budget_le`).
Vacuous for any realistic manifest; `demoManifest` satisfies it by
`decide`-scale arithmetic. -/
structure Fits (m : Manifest) : Prop where
  period_lt : ∀ d : DomainId, (m.doms d).periodP < 2 ^ 32
  maxdon_lt : ∀ d : DomainId, (m.doms d).maxDonation < 2 ^ 32

/-! ## Reset -/

/-- Reset abstracts to boot: decoding the declared reset values recovers
`m.initState` field by field. -/
theorem abs_reset (m : Manifest) :
    Hw.abs (Hw.core m).reset = m.initState := by
  sorry

/-- The coupling holds at reset (`cycle = 0`, `rctr = 0 % P`, all encodings
canonical by construction). -/
theorem coupled_reset (m : Manifest) : Coupled m (Hw.core m).reset := by
  sorry

/-! ## The commuting square and coupling preservation -/

/-- **The R-MC square**: below the counter horizon, one core cycle is
exactly one spec step through `Hw.abs`. Hypotheses: manifest WF (scheduler
determinism) and datapath fit, the hidden-state coupling, reachability on
both sides (spec-side range invariants — budgets `≤ Q`, `depth <
maxChainDepth`, `cyclesLeft ≤` max cost, mover regions valid — and the
concrete-side mark-engine state), and no counter wrap this cycle. -/
theorem square (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hwrap : (Hw.abs σ).cycle + 1 < 2 ^ 32) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The coupling is preserved by one core cycle (below the horizon). -/
theorem coupled_step (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hwrap : (Hw.abs σ).cycle + 1 < 2 ^ 32) :
    Coupled m ((Hw.core m).cycle σ) := by
  sorry

/-! ## Assembly (sorry-free given the square) -/

/-- `Design.run`'s successor on the right (its definition recurses on the
left). -/
private theorem design_run_succ (dz : Loom.Hw.Design) :
    ∀ (n : Nat) (σ : Loom.Hw.St),
      dz.run (n + 1) σ = dz.cycle (dz.run n σ) := by
  intro n
  induction n with
  | zero => intro σ; rfl
  | succ k ih =>
      intro σ
      show dz.run (k + 1) (dz.cycle σ) = _
      rw [ih (dz.cycle σ)]
      rfl

/-- Spec states along the run from boot are reachable. -/
theorem machine_reachable_stepN (m : Manifest) (n : Nat) :
    (machine m).Reachable (stepN m n m.initState) := by
  induction n with
  | zero => exact .init rfl
  | succ k ih =>
      rw [Wip.stepN_succ]
      exact .step ih rfl

/-- Core states along the run from reset are reachable. -/
theorem core_reachable_run (m : Manifest) (n : Nat) :
    ((Hw.core m).toTSys).Reachable ((Hw.core m).run n (Hw.core m).reset) := by
  induction n with
  | zero => exact .init rfl
  | succ k ih =>
      rw [design_run_succ]
      exact .step ih rfl

/-- The lockstep induction: abstraction equality and coupling, jointly. -/
theorem lockstep_coupled (m : Manifest) (hwf : m.WF) (hfit : Fits m) :
    ∀ n : Nat, n < 2 ^ 32 →
      Hw.abs ((Hw.core m).run n (Hw.core m).reset) = stepN m n m.initState ∧
      Coupled m ((Hw.core m).run n (Hw.core m).reset) := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨abs_reset m, coupled_reset m⟩
  | succ k ih =>
      intro hk
      obtain ⟨habs, hcpl⟩ := ih (Nat.lt_of_succ_lt hk)
      have hcr := core_reachable_run m k
      have hsr : (machine m).Reachable
          (Hw.abs ((Hw.core m).run k (Hw.core m).reset)) := by
        rw [habs]; exact machine_reachable_stepN m k
      have hwrap : (Hw.abs ((Hw.core m).run k (Hw.core m).reset)).cycle + 1
          < 2 ^ 32 := by
        rw [habs, stepN_cycle]
        show 0 + k + 1 < 2 ^ 32
        omega
      refine ⟨?_, ?_⟩
      · rw [design_run_succ, square m hwf hfit _ hcpl hcr hsr hwrap, habs,
          Wip.stepN_succ]
      · rw [design_run_succ]
        exact coupled_step m hwf hfit _ hcpl hcr hsr hwrap

/-- **R-MC.** Exact whole-state lockstep on the 32-bit counter horizon:
after any `n < 2 ^ 32` cycles from reset, decoding the core's register
file yields precisely the ISS state after `n` steps from boot. (The
formal generalization of the `Tests/Lnp64uCore.lean` lockstep runs; see
the module docstring for why the horizon is inherent.) -/
theorem abs_run (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    {n : Nat} (hn : n < 2 ^ 32) :
    Hw.abs ((Hw.core m).run n (Hw.core m).reset) = stepN m n m.initState :=
  (lockstep_coupled m hwf hfit n hn).1

/-- **R-MC transport.** Every ISS invariant — in particular each of T2–T9's
invariant forms — holds of the abstraction of every core state on the
horizon. This is the theorem that carries the ledger onto the emitted
Verilog. -/
theorem invariant_transport (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    {P : MachineState → Prop} (hP : (machine m).Invariant P)
    {n : Nat} (hn : n < 2 ^ 32) :
    P (Hw.abs ((Hw.core m).run n (Hw.core m).reset)) := by
  rw [abs_run m hwf hfit hn]
  exact hP _ (machine_reachable_stepN m n)

end Machines.Lnp64u.Theorems.RMC
