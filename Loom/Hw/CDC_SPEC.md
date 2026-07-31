# CDC/metastability spec (D21 candidate) — binding decisions

Goal: the wrapper's clock-domain crossings stop being prose and become
(a) an enumerated, stated contract and (b) a small verified protocol
theorem — the first metastability-aware proof in the repo. We do NOT
verify physics: the single physical assumption (a metastable first flop
resolves by the next edge — the MTBF assumption) is encoded structurally
as a hypothesis, and everything above it is proved for ALL adversarial
resolutions.

## Part A — the contract inventory (DESIGN.md §D21 + a TCB.md entry)

Enumerate, from `fpga/zc702/lnp64mini_soc_top.v` / `lnp64mini_dual_top.v`:
1. UPDATE→sysclk command path: fields latched in the UPDATE domain, then a
   toggle through a 2FF sysclk synchronizer, XOR pulse. Assumption: JTAG
   UPDATE events ≥ k sysclk cycles apart (scans are µs, sysclk is 40 ns —
   margin ~10^2); fields stable from latch until the pulse.
2. sysclk→DRCK read-back captures (2FF samples of o_* values): per class —
   quasi-static latched values (reg_rd, rd_reg, frozen state) vs
   tear-tolerant liveness counters (heartbeat, fclk). State which is which.
3. POR counters: reset-release synchronization.
4. The MTBF/physical assumption, stated once, as the D21 trust boundary.

## Part B — the verified toggle-sync (new file Loom/Hw/CdcContract.lean)

Plain Lean model (NOT a Design — nondeterminism is the point):

- Events: `E : Nat → Bool` marks sysclk indices at which the source toggle
  flips (an abstract stand-in for UPDATE edges).
- State: toggle `T`, sync flops `s0 s1 s2 : Bool`.
- Metastability model: when the toggle flips "close to" s0's sampling edge
  (same cycle as the flip), s0's sampled value is chosen adversarially by
  an oracle `res : Nat → Bool` (it may see old or new T); by the NEXT
  cycle s0 samples the settled T deterministically. s1 := s0, s2 := s1
  are clean (that is the 2FF guarantee = the stated assumption).
- `pulse n := s1 n ≠ s2 n` (the wrapper's `t1 ^ t2`).

Theorem (`toggleSync_sound`), ∀ E res: if events are ≥ 4 cycles apart
(`E n → E m → n ≠ m → |n−m| ≥ 4`), then:
  (a) every event at n yields EXACTLY one pulse, at n+2 or n+3
      (adversarial resolution decides which);
  (b) pulses are 1 cycle wide;
  (c) no pulse occurs without an event (no spurious wakeups).
Prove by induction with case analysis on `res`. Keep the model minimal —
Bool streams and a step function; avoid over-generalizing.

- `CmdPulseTrace (k : Nat) (ιs : Nat → InEnv) : Prop` — the trace class
  the wrapper delivers to a D15 design: cmd_valid is a 1-wide pulse train
  with spacing ≥ k, and cmd_idx/cmd_data are constant from (pulse − 2) to
  the pulse cycle. Lemma `toggleSync_cmdPulseTrace`: composing the model
  with latched-fields (fields change only at events) yields a
  `CmdPulseTrace k` for k = spacing − 3.
- Downstream hook (statement only, docstring): design-level theorems over
  open designs may assume `CmdPulseTrace k ιs` — this is the precise
  interface between wrapper physics and Lean proofs.

## Deviations (recorded 2026-07-31, at implementation)

Everything asked for is proved with no sorry and no axiom (both headline
theorems close over `[propext, Quot.sound]`). Two clauses changed shape:

1. **Field-stability window: one pre-pulse cycle, not two.** Part B asks
   `CmdPulseTrace` to require `cmd_idx`/`cmd_data` constant from
   `pulse − 2` through the pulse. That is not deliverable by any
   resolution-agnostic argument, and the model shows why: the fastest
   resolution (`res n = true`) puts the pulse at `n+2`, while the fields
   are latched by the *same* `UPDATE` edge that flips the toggle, so their
   sysclk-visible value is only guaranteed settled from `n+1`. The window
   `[n, n+2]` therefore straddles the field change; `[n+1, n+2]` does not.
   Shipped: `idxStable`/`dataStable` demand equality across
   `(pulse − 1, pulse)`, i.e. one full setup cycle before the pulse, which
   is what the hardware guarantees and what a design sampling at the pulse
   edge (with or without one stage of input pipelining) needs. Reading
   "pulse − 2" as counting from the *latch* cycle recovers the spec's
   intent exactly; only the index is off by one.
2. **Pulse spacing `k − 1`, stronger than the requested `k − 3`.**
   `toggleSync_cmdPulseTrace` delivers `CmdPulseTrace (k-1)` from
   `Spaced k E` (`k ≥ 4`): consecutive pulses are worst-case
   `(n'+2) − (n+3) = (n'−n) − 1 ≥ k−1` apart. The spec-shaped
   `CmdPulseTrace (k-3)` is kept as the corollary
   `toggleSync_cmdPulseTrace'`, via `CmdPulseTrace.mono`.

Two additions beyond the letter of the spec, both cheap and load-bearing:
`CmdPulseTrace.quiet` (no pulse in the first two cycles — the synchronizer
is flushing; without it the class is satisfiable by traces the model never
produces), and the sharp `pulse_at_event` (`pulse (n+2) = res n`,
`pulse (n+3) = !res n`), from which the requested "exactly one pulse"
clause is a two-line corollary and which states precisely that the
adversary chooses the pulse's *latency* and nothing else.

Constraints: additive files only (CdcContract.lean; DESIGN.md gains §D21;
TCB.md gains the stated assumption). No sorries anywhere; if a clause of
the theorem resists proof, WEAKEN THE STATEMENT to what is proved and
record the gap in §Deviations here — never ship an axiom or sorry.
`lake build` + `lake exe audit` green.
