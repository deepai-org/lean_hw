# Multiclock RTL and physical boundary

This document states the exact trust boundary between Loom's checked
multiclock semantics, its generated CDC RTL, and physical clock-domain
crossing behavior. It is the multiclock counterpart to
[`CONCRETE_SSA_BOUNDARY.md`](CONCRETE_SSA_BOUNDARY.md).

## Machine-checked facts

The following claims are inside Lean's theorem boundary:

- a checked named `System` contains every declared island and channel and uses
  its stored `ClockRel` for executable replay and schedule-quantified
  invariants;
- the abstract bounded `Chan` semantics is equivalent, for every finite trace,
  to the generated synchronous `Design` adapter;
- the executable toggle-mailbox and asynchronous-FIFO models refine the same
  abstract channel, including accepted and delivered traces;
- the FIFO uses finite ring addresses, proves simultaneous successful ports
  distinct, and therefore discharges `AsyncQueueStorage.CollisionFree` for
  every event; any implementation of that technology-neutral contract then
  composes into the same arbitrary-trace channel refinement;
- `CertifiedSystem` preserves certified-DAG/semantic agreement for every
  island across replay and derives its comparison/coverage surface from all
  island coordinates and bounded-channel slots; its constructor also requires
  an explicit `Chan.Refinement` for every declared connection;
- the structured channel-instance list consumed by top-level rendering and
  the structured groups consumed by the neutral physical-intent renderer each
  cover the checked connection list exactly once and in declaration order;
- the stock portable binding derives both exact ordered two-stage
  synchronizer chains and both exact Gray launch/first-capture buses, with
  period-relative skew and datapath requirements, from the same selected
  connection and generated hierarchy;
- every distinct generated clock domain has an exact reset-delivery record,
  and the full timing-plus-reset requirement list is the indexed domain of a
  fail-closed backend report; and
- binary-reflected Gray encoding has a machine-checked one-bit transition
  property. `Cdc.Gray.succ_xor_oneBit` proves that successive encodings have a
  power-of-two XOR, `succ_differs_exactly_one` gives the pointwise unique-bit
  statement, `succ_xor_oneBit_within` bounds the changing bit before
  finite-width wrap, and `wrap_xor_oneBit` proves the wrap transition. The
  executable FIFO's read and write steps are connected to this fact by
  `AsyncFifo.readGray_step` and `writeGray_step`.

Thus the semantic property that motivates a Gray-pointer synchronizer—one
pointer bit changes at a time—is machine-checked, including wraparound.

`AsyncFifo.sampledPointerHistoryValidity` is the separate named sampling
result: every admitted code is an exact codeword from an earlier point in the
source's unbounded generation history, and successive observations never move
backward in that history. Numeric monotonicity of the finite wrapped pointer is
not the claim. Staleness may be unbounded for safety; bounded staleness is an
additional progress premise.

## Trusted CDC RTL correspondence

Generic Loom no longer contains stock handwritten toggle or Gray-FIFO
SystemVerilog generators. The former Gray renderer is retained under
`Evidence.ReferenceCdcRtl`, explicitly outside the certified path; Lean has
not proved that evidence text implements the executable FIFO machine. A
`system.v` produced with that evidence binding therefore has a wider trusted
text boundary than ordinary single-clock RTL and is only an integration
artifact.

The certified portable route instead compiles every control register, Gray
increment, synchronizer stage, flag comparison, and arbitrary power-of-two
register-bank storage operation as an ordinary per-domain `Design`. Each
component is a `CertifiedDesign`;
`AsyncFifoDesign.Compiled.refinement` joins their transition equations to the
single parametric channel theorem. `CertifiedPortableBinding` carries only
those fixed compiled controls and a proved generated storage witness for the
exact channel width and depth. `CertifiedSyncBinding` independently packages
the ordinary proved synchronous FIFO for every positive depth when endpoint
clocks agree.

`CertifiedRealizedSystem` requires those bindings in the same ordered key
domain as the checked System connections. Its renderer adds only structural
module instantiation and wiring around the exact compiler projections. The
mechanical CDC-boundary gate rejects behavioral RTL tokens in that renderer.
Its `rtlArtifact` is the literal `system.v` member traversed by `emit`, and
`verifiedReleases` carries both membership and exact UTF-8 equality. Thus the
portable certified path has no trusted behavioral CDC RTL correspondence
step. As with the single-clock path, interpretation of the resulting Verilog
text by downstream tools remains outside the theorem.

An optional FPGA or ASIC storage macro replaces only the register-bank leaf.
That route is conditional on one named, configuration-matched assertion that
the physical macro satisfies `AsyncQueueStorage`; it does not weaken or alter
the unconditional portable artifact.

## Physical boundary

Metastability is categorically outside Loom's digital semantics. Gray
adjacency supplies the checked digital premise for the usual physical
argument, but Loom does not prove that a synchronizer resolves within an
aperture, meets an MTBF target, is placed or routed correctly, or receives the
required timing constraints in a downstream tool.

Generic emission now states substantially more than an asynchronous clock
pair: it names the exact synchronizer registers and coherent Gray buses and
records their relative physical requirements without selecting vendor syntax.
It also states, per clock domain, that the current shared active-high reset is
sampled synchronously, requires that domain to tick while asserted, and may be
released on independently observed domain ticks. This is still intent, not
signoff or a physical reset tree. A proof-carrying `PhysicalCheckReport` must
cover the exact ordered timing-plus-reset requirement list and classify every
item as `PASS`, `SKIP`, or `UNCONSTRAINED`; generic emission never invents
physical `PASS`. The reference backend validates this exact-coverage
extension seam. Production XDC, SDC, Quartus, and ASIC lowering/checking remain
optional evidence-layer integrations.

The physical argument therefore remains explicit: if only one Gray transition
is in flight at the sampling boundary, inter-bit skew is within the declared
constraint, and the receiving synchronizer resolves the changing bit before
use, the sampled code is the old or new adjacent code rather than a fabricated
mixture. Gray adjacency proves the digital single-transition premise; it does
not by itself prove that a fast source cannot place two different Gray
transitions inside the physical aperture. The rate/skew premise, analog
resolution, implementation of synchronizer cells, and MTBF calculation are
not machine-checked.

The storage boundary is similarly narrow. The FIFO proof must establish the
schedule-native ownership chain `write → synchronized publication → read →
synchronized publication → slot reuse`, which makes same-address collisions
unreachable. The compiled generated register-bank realization satisfies the
digital storage contract without an external assumption: its proof unfolds
the ordinary write- and read-domain `Design.cycleOpen` transitions, and the
parametric FIFO theorem consumes that proved implementation directly. A vendor dual-clock RAM or
ASIC SRAM macro is admitted only through one named, configuration-matched
assumption that it satisfies the same width/depth/read-latency contract.

## Independent reset boundary

`SystemResetPolicy.independentFlush` is an executable abstract recovery
contract, not a claim about the current emitted reset tree. Its replay event
resets named islands, discards all queued and same-event traffic on incident
channels, holds those queues empty for the event, and leaves nonincident
channels on their ordinary transition. Capacity preservation under legal
recovery traces is machine-checked.

`Chan.RecoveryRefinement` names the completion/linearization event and records
the complete queue discarded at that event. A technology-neutral four-phase
request/acknowledgement model proves the channel-local interface for arbitrary
schedules; held clocks stutter, traffic is blocked as each side joins recovery,
and a held-high request coalesces into one epoch. A separate coordinated view
handles islands with several incident channels: it retains an early-reset
channel's logical epoch until one global commit. Its endpoint controllers are
ordinary `Design`s, and the pair of actual compiler-source states is proved to
take exactly the coordinated endpoint transition for arbitrary states and
inputs.

The stock recovery binding now joins both compiled endpoint controllers,
compiled traffic/reset guards, and the ordinary compiled portable FIFO using
structural wiring only. The generated top exposes a level request/completion
pair per island, folds all incident endpoint completions with a compiled
coordinator cell, and asserts reset only for the requesting island after
quiescence. The structured coordinator domain has a checked theorem that both
physical halves of every incident channel are present. `RealizationPlan.recoveryPortable` exposes this through the
ordinary application facade. The emission gate requires a recovery-capable
binding for every `independentFlush` connection and rejects such a binding
under coordinated reset; the same compatibility is carried as a constructor
proof in `CertifiedRealizedSystem`.

The generated endpoint holds its local FIFO half in reset for the complete
`flushed` phase, rather than issuing a one-cycle pulse. Thus a half that
finishes early cannot resume sampling a peer pointer from the old epoch.
`completes_bothResetHeld` proves both completion edges asserted reset, and the
endpoint's `flushed` level keeps it asserted until four-phase release. The
system theorem `recoveryComplete_holds_all_compiledEndpointResets` then lifts
that fact through the exact structured coordinator domain: reported island
completion implies every incident compiled endpoint's reset-hold expression
is high. The three-clock smoke test additionally checks all incident controls and
synchronizer registers are at the common empty origin while `recovered` is
high.

Global event alignment is now machine-checked rather than assumed.
`recoveryComplete_incident_both` extracts both exact halves of every incident
channel from the generated coordinator domain;
`coordinatedProtocol_event_eq_systemRecovery` turns that completion into one
common logical commit; and
`recoveryPortable_globalCommit_refines_advanceRecovery` joins the selected
binding's queue and loss accounting to the exact per-channel System
projection. This specifically handles channels that finished resetting on
different earlier clocks.

What is not yet one machine-checked statement is the final physical-state
composition: the compiled FIFO controls, register-bank storage, and datapath
guards must be related through those early local reset intervals and shown to
re-establish the empty representation at the proved global commit.
`islandCompiledReset_refines_advanceRecovery` uses the generic
compiler theorem for synchronous-reset edges to join every exact certified
island module directly to the reset state in `System.advanceRecovery`.
The endpoint cycle equation, datapath masks/resets, component certification,
coordinator certification, and exact ordered assembly coverage are checked
separately.
A three-clock Icarus test exercises a requested island incident to two
channels, checks all four endpoint completions and peer-reset containment, and
then returns to service. It remains wiring/execution smoke evidence. This gap
must stay named until the composed transition theorem closes it.

The graceful protocol assumes a recovery request is sampled while each
participating channel clock eventually ticks. Abrupt power removal, clocks
that never return, asynchronous pulse capture, electrical reset distribution,
and reset sequencing of external hard IP remain named physical/system
obligations rather than consequences of the digital theorem.

## External evidence

Icarus Verilog compiling and simulating a generated two-clock `system.v` is a
smoke test of syntax, elaboration, wiring, and one idealized digital execution.
It is not corroboration of the refinement theorem and is not evidence about
metastability, timing closure, MTBF, placement, routing, or silicon behavior.

Synthesis, CDC analysis, timing reports, implementation manifests, and board
tests remain separately identified external evidence under [`TRUST.md`](TRUST.md).
