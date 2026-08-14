# Loom multiclock design and tooling feedback

This document contains practical feedback from using Loom's multiclock APIs,
semantics, proofs, compiler, and evidence tooling. It is not a project diary,
test report, release claim, or record of campaign results.

## Design model and API

### What works well

- `SystemBuilder` gives a clear architectural vocabulary. Ordinary `Design`
  islands, named clocks, typed channels, connection direction, and clock
  relationships remain separate concepts, so a multiclock topology is visible
  without reading CDC implementation details.
- `withSource` and `withSink` keep handshake state and CDC machinery out of
  application islands. Application code sees typed enqueue/dequeue operations
  while realization remains a separate choice.
- Keeping arbitration and routing in ordinary `Design` logic is the right
  boundary. CDC channels transport ordered values; they do not acquire hidden
  many-to-one, routing, or fairness semantics.
- A mixed realization can use synchronous queues for aligned endpoints and
  Gray FIFOs for unrelated endpoints within one checked system. Multiclock
  support therefore does not force unnecessary CDC logic onto every route.
- `PackedChan` works well for realistic protocols. Field-oriented application
  logic and a single derived packed layout are much safer than repeating flat
  widths and bit offsets across islands, wrappers, and tests.
- The reserved generated-endpoint namespace and exact connection inventory
  make undeclared cross-domain dependencies difficult to introduce
  accidentally. Missing, duplicated, reordered, or malformed bindings fail at
  a useful structural boundary.
- The explicit coordinated-reset contract is preferable to an implicit promise
  that arbitrary unilateral reset is safe. Unsupported recovery behavior
  should continue to be rejected rather than approximated.
- The independent-flush realization composes cleanly on a realistic
  bidirectional graph. Selecting one recovery-capable implementation per route
  produces the expected per-island completion fold over both halves of every
  incident channel; the application topology does not need recovery-specific
  CDC wiring.
- Keeping the logical `System` fixed while substituting a registered physical
  storage leaf is a useful realization boundary. Once read presentation is
  explicit, the target wrapper can absorb the extra stage, report different
  timing, and preserve the same certified channel refinement and application
  behavior.

### What could improve

- The boundary between stable public proof API and internal `System`
  implementation helpers is unclear. Proofs routinely need resolved island
  inputs, connection events/results, channel queues, and channel-state update
  facts. These deserve a documented supported interface.
- Large application rules should be encouraged to have stable names.
  Writer-support projection is effective on named rules, whereas repeated
  anonymous actions inside a `Design` literal create large and fragile proof
  terms.
- Reset should be represented as a first-class domain policy with an explicit
  implementation strategy. In particular, common logical reset does not by
  itself specify safe physical deassertion across unrelated clocks.
- Loom should distinguish named clock domains from independent physical clock
  references in its evidence vocabulary. They have the same schedule-level
  semantics but support different physical claims.
- Optional observation interfaces would help evidence builds. Queue occupancy,
  coherent snapshots, and fault injection are useful for exercising reset and
  backpressure, but currently tend to require target-specific RTL derivatives.
- `System.applyRecovery` makes the loss semantics unambiguous, but it does not
  return an aggregate loss ledger. A user testing a multi-route island must
  traverse every connection, repeat the `affects` test, and snapshot each queue
  before the transition. A small `RecoveryResult` containing the next state and
  per-route discarded values would make the advertised loss-explicit contract
  much harder to measure incorrectly.
- Independent channel recovery does not notify application peers which logical
  requests were discarded. That is a reasonable scope boundary—retry,
  deduplication, and epoch policy belong to the protocol—but the application
  facade should say directly that forward progress after a lossy island reset
  requires such a protocol or an explicit fresh application epoch.

## Semantics and execution

### What works well

- Named-clock events are an effective semantics for unrelated clocks. Empty
  events, single-domain ticks, coincident ticks, pauses, and changing relative
  order can all be expressed without choosing a global clock ratio.
- Safety arguments naturally quantify over arbitrary finite event lists. This
  makes it straightforward to keep fairness and clock-frequency assumptions
  out of conservation, ordering, and capacity claims.
- Simultaneous source acceptance/replacement and simultaneous FIFO push/pop are
  modeled precisely. The semantics preserve the distinction between a channel
  queue and its registered source and sink endpoint state.
- A compact evaluator can be related to `System.runEventsFrom`; the semantic
  model is precise enough to support a checked optimized runner rather than an
  unrelated reference simulation.

### What could improve

- General certified execution retains more state and proof structure than is
  practical for large campaign loops. Loom would benefit from a generated
  compact runner and a reusable correspondence theorem for every certified
  `System`.
- Proving optimized-runner correspondence requires repetitive string, name,
  width, and `Option` case analysis. A public theorem exposing the resolved
  input environment and connection event for each certified connection would
  remove much of this work.
- One-bit control values move frequently among `BitVec 1`, Boolean tests,
  `toNat`, and propositions. A small normalization library for Boolean
  registers and guards would make semantic proofs shorter and more stable.
- `System.State` permits malformed, over-capacity channel states. Application
  induction therefore has to carry reachability and capacity facts explicitly.
  A reachable-state induction principle that supplies certified channel bounds
  would better match normal proof use.
- Finite protocol projections are very useful for schedule exploration, but
  Loom lacks a standard way to define a projection, prove that it commutes with
  execution, and turn a checked finite certificate into a theorem.

## Safety-proof ergonomics

### What works well

- `System.channelTraceConservation`, `Chan.sourceStep_conservation`, and
  `Chan.sinkStep_conservation` provide the correct schedule-independent base
  laws. They do not smuggle in fairness or clock-ratio assumptions.
- `Design.regSupportRules` and `memSupportRules` are powerful refinement tools.
  They allow proofs to isolate semantic writers while discarding endpoint
  maintenance, progress counters, and unrelated rules by checked footprints.
- The read-prestate/write-accumulator semantics is expressive enough to relate
  literal actions to abstract memory and response models without introducing a
  second transition system.
- Registered endpoint conservation has a sound finite-cut interpretation.
  Produced values may reside in the source register or FIFO; consumed values
  may still be represented by a coherent pending pop. Drained equalities then
  follow as explicit corollaries.
- Tagged histories are an effective way to combine payload conservation with
  application routing state. They preserve the separation between generic CDC
  ordering and application-defined requester association.

### What could improve

- The public theorem layer remains too close to individual channels. A natural
  end-to-end theorem still needs substantial custom invariants spanning source
  endpoints, FIFO contents, sink endpoints, and application rules.
- Loom needs generic `withSource` and `withSink` refinement theorems. Given an
  application observation of produced or consumed values, these should expose
  the registered endpoint step, conservation equation, and head coherence
  without repeating input and register projections.
- A source/sink ledger composition library should provide non-overlapping
  logical occupancy views. A pending sink pop and the physical FIFO head are
  two views of the same value; naive concatenation double-counts it.
- Routed transaction systems need a helper for composing payload histories
  with application-defined metadata such as client, tag, or route. This should
  remain generic and must not add routing semantics to `Chan` itself.
- Local `cycleOpen` proofs expand into nested `Act.run`, `RegEnv.set`, generated
  endpoint names, and guard normalization. Focused simplification lemmas for
  declared inputs, endpoint registers, and named rules would reduce noise.
- Action lemmas need to account for arbitrary accumulators and preserved memory
  views to compose cleanly with `Design.cycleOpen`. The library could offer a
  standard rule-refinement pattern that makes this requirement explicit.
- A reusable rule-event/history theorem would help lift a local rule firing to
  a named-clock history without a custom induction for every application.

## Progress and liveness

### What works well

- Loom's event semantics makes the safety/liveness boundary clear. Conditional
  progress can name continued ticking, downstream consumption, available
  capacity, and arbitration opportunities independently of safety.
- A small protocol projection and local rank can describe arbitrary changing
  clock order more convincingly than a collection of fixed schedules.
- Deduplicating equivalent projected states makes finite local certificates
  much more practical than replaying every schedule path independently.

### What could improve

- Loom needs compositional progress contracts for channels and islands. Users
  should be able to combine bounded ticking, eventual consumption, and a local
  stream contract without constructing an application-specific global search.
- Public progress premises should have Boolean checkers with soundness theorems
  and useful counterexamples. Recursive propositions are readable in theorem
  statements but awkward in executable fixtures and schedule generators.
- Large `native_decide` searches are a poor default proof artifact: they are
  expensive and introduce `Lean.trustCompiler`. A staged certificate format
  with a small kernel-checked verifier would give better performance and a
  clearer trust boundary.
- Large literal schedule lists elaborate poorly. A compact block or repeated
  schedule representation would make bounded proofs and regression fixtures
  easier to state.
- Transfer-accounting and rank libraries should support integer-valued
  conservation directly. Natural subtraction can hide mistakes around
  registered pending transfers.

## Compiler and artifact tooling

### What works well

- Exact-byte artifact generation is a strong interface. It cleanly separates
  proof-only changes from hardware changes and lets downstream evidence bind to
  literal emitted RTL.
- The checked realization inventory ties each logical connection to an exact
  synchronous or asynchronous implementation choice.
- Emitting crossing, synchronizer, Gray-bus, reset, and clock intent alongside
  RTL makes the physical obligations reviewable without embedding one vendor's
  constraint language in Loom's semantics.
- Fail-closed regeneration and byte comparison are useful operationally. An
  incomplete backend environment cannot silently turn a partial run into a
  successful result.
- A single producer for RTL, inventories, manifests, hashes, campaigns, and
  axiom output is easier to audit than several loosely related scripts.

### What could improve

- Evidence generation should provide a standard kernel-only axiom policy. It
  is too easy for a local `native_decide` to introduce `Lean.trustCompiler`
  into a theorem that otherwise appears proof-only.
- The compiler needs downstream-parser tests in addition to expression
  semantics. Legal denotation does not guarantee that every emitted construct,
  especially zero-width concatenation cases, is accepted by real HDL tools.
- Multiclock tooling needs target-specific constraint lowering with an explicit
  capability report. Unsupported generated clocks, asynchronous clock groups,
  synchronizer attributes, or Gray-bus constraints should be classified as
  unsupported or unconstrained, never silently discarded.
- Backend adapters should consume Loom's physical-intent inventory directly and
  report requirement-by-requirement coverage. Ad hoc scripts for synchronizer
  placement and bus constraints are hard to keep aligned with the certified
  connection inventory.
- Root provenance, measured activity, tool versions, routing seed, routed
  design identity, and bitstream identity should be standard evidence fields.
  These are general multiclock tooling needs, not facts that each board harness
  should encode in prose.
- A cached artifact-verification mode followed by a concise prerequisite report
  would improve board bring-up. Replaying a large Lean dependency graph before
  reporting missing physical tools creates unnecessary diagnostic noise.
- A stable focused multiclock CI target would shorten iteration compared with
  rebuilding an umbrella test graph.

## Hardware-facing usability

### What works well

- Technology-neutral RTL and a separate physical-intent inventory are the
  correct boundary. Vendor implementation evidence can strengthen confidence
  without becoming a dependency of Loom's generic semantic claim.
- A contended, bidirectional transaction fabric with mixed synchronous and
  asynchronous routes is a realistic enough subsystem to validate the
  abstraction boundary. Arbitration, requester/tag routing, masked memory
  operations, lossless telemetry backpressure, and checking remained ordinary
  island logic; Loom's multiclock layer remained transport and realization.
- Typed configuration inputs are preferable to post-emission RTL edits for
  traffic limits and evidence modes. They preserve one canonical artifact
  across short and prolonged runs.
- Existing application counters, sticky errors, ordering checks, and rolling
  digests form a useful compact observation surface for long multiclock tests.

### What could improve

- Physical reset release across unrelated clocks needs backend assistance.
  A shared synchronous-reset signal is not enough to guarantee robust release;
  the target adapter may need clock gating or per-domain release handling while
  preserving the declared coordinated-reset semantics.
- Host-driven clocks are valid independent roots but couple clock progress to
  the control and observation transport. Tooling should record that distinction
  and help harnesses avoid control-protocol faults that resemble CDC failures.
- Optional coherent snapshot support would prevent multi-register status reads
  from combining different logical instants.
- Fault injection should target a typed field and a transaction predicate, not
  merely a flat payload bit and occurrence number. Otherwise a mutation can hit
  a semantically irrelevant field and create a misleading negative control.
- Evidence tooling should distinguish free-running independent oscillators,
  derived clocks, gated domains, and host-driven independent clocks. Treating
  all of them as simply “multiple clocks” is too imprecise for physical review.
- The first target-storage substitution attempt exposed an underspecified
  physical contract: `readLatency = 1` did not say whether the addressed word
  was continuously visible or returned after an enabled read edge. The API now
  distinguishes first-word-fall-through and registered presentation and
  requires the matching proof at the wrapper boundary. That fail-closed split
  was necessary; width, depth, and a latency number alone were not enough to
  wire a real synchronous block RAM safely.
- Registered target storage currently needs a dedicated conservative wrapper
  with a one-word presentation buffer. Generalizing this beyond the two known
  presentations, or supporting a throughput-optimized prefetch controller,
  would need a richer request/response timing contract rather than more ad hoc
  numeric latency fields.
- Equal-shaped target leaves initially caused duplicate compiled source/sink
  module declarations because those control names were derived only from FIFO
  shape. Scoping opaque target-control modules by connection fixes the emitted
  artifact. In general, artifact assembly should treat per-binding module-name
  uniqueness as a checked invariant, not rely on widths and depths happening
  to differ.

## Scope assessment from handwritten HDL and Tcl

No handwritten Verilog was needed for the multiclock application itself. The
island logic, packed protocols, arbitration, routing, memory behavior, channel
endpoints, synchronous queues, and asynchronous Gray FIFOs all remained in Loom
and its generated `system.v`. That is strong evidence that Loom's core language
scope is already appropriate.

Handwritten Verilog was used in four surrounding roles:

- The board shell instantiated FPGA-specific clock and debug primitives such as
  differential input buffers, global clock buffers, the processing-system clock
  source, and the boundary-scan primitive. It also connected LEDs and the
  generated `loom_system`. This is proper target-shell work; generic Loom should
  not need to model every vendor primitive.
- The board shell implemented clock gating and a safe coordinated-reset release
  adapter. Clock gating for adversarial tests belongs in the target harness.
  Reset release is a more substantive gap: Loom declares the logical reset
  policy, but no backend interface realizes that policy safely for unrelated
  physical clocks. Asking for a reset-realization contract in target-adapter
  tooling is in scope; adding vendor clock primitives to the core semantics is
  not.
- A handwritten boundary-scan register block provided configuration, coherent
  control, identity checking, and readback. A board-specific JTAG transport is
  appropriately external. A generic generated evidence/control register map
  could reduce boilerplate, but it should be optional tooling rather than part
  of functional Loom semantics.
- Test-only RTL variants exposed FIFO occupancy and injected a controlled
  payload fault. An early long-run variant also changed a literal transaction
  bound; making that bound a normal typed Loom input eliminated the need for
  that edit in the later design. Optional channel-observation and typed
  fault-injection facilities are reasonable evidence-tooling requests because
  they avoid modifying emitted internals, but production Loom designs should
  not expose such state by default.

Handwritten XDC/Tcl-like constraints fell into two categories. Pin locations,
I/O standards, oscillator periods, and vendor hierarchy are necessarily board
specific and should remain outside generic Loom. In contrast, lowering Loom's
neutral clock-group, synchronizer, and Gray-bus intent into the exact commands
supported by a selected backend is an in-scope tooling improvement. The backend
should also report unsupported intent explicitly instead of requiring a shell
script to strip rejected commands or patch placement after synthesis.

The XSDB Tcl scripts programmed the FPGA, spoke the JTAG register protocol,
paused clocks, polled counters, and evaluated campaign outcomes. None of that
was forced by a missing Loom language construct; it is ordinary external test
orchestration. A generated host client from a declared evidence register map
would be convenient, but absorbing board programming and campaign control into
Loom would broaden its scope without improving the hardware abstraction.

The resulting scope judgment is therefore: do not substantially enlarge Loom's
core multiclock language. The justified additions are narrow facilities at its
existing boundaries:

1. a target-adapter contract for physical clock provenance, constraint lowering,
   and coordinated-reset realization;
2. optional generated observation, coherent snapshot, and typed fault-injection
   support for evidence builds; and
3. generated register-map metadata or host bindings so target harnesses need
   less handwritten transport glue.

Vendor primitives, board pin constraints, bitstream programming, JTAG command
sequences, and campaign policy should remain external.

## Highest-value improvements

1. Add generic registered `withSource`/`withSink` refinement and ledger
   composition theorems.
2. Generate a compact certified `System` runner with a reusable semantic
   correspondence proof.
3. Provide reachable-state induction with channel capacity and endpoint
   coherence facts supplied automatically.
4. Add compositional progress contracts and a staged, kernel-checked finite
   certificate format.
5. Define a target-adapter interface for constraint lowering, reset release,
   physical clock provenance, and requirement coverage.
6. Standardize kernel-only axiom auditing, coherent observation, and typed
   runtime fault injection in the evidence tooling.

## Physical follow-on: recovery observation and target storage (2026-08-14)

The recovery-capable artifact worked on the ZC702 with the genuinely unrelated
CPU/fabric, DMA, memory, and JTAG-monitor roots. Fabric-only recovery completed
its generated 12-endpoint handshake under load, discarded two incident
transactions explicitly, preserved and drained four audit records on the
unaffected crossing, and completed a clean 256-per-client epoch after common
reset. This is useful evidence that Loom's recovery protocol is practical in a
real shell and is not dependent on closely aligned simulator clocks.

One integration detail was easy to misunderstand. Follow-up inspection of the
generated coordinator and endpoint state shows that `fabric__recovered` is not
a one-cycle pulse: it is the live level `recover && all incident endpoints
complete`, and endpoint completion remains held while `recover` is held. A
slow JTAG poll missing it therefore points to the shell/transport observation
path or request lifetime, not to Loom intentionally emitting a pulse. Loom now
states this waveform in typed generated interface metadata and in the physical
report. A transport-specific sticky latch may still be convenient, but it is
external observation plumbing rather than a Loom recovery-semantic feature.

The target-storage follow-on found and then isolated a real target failure. The
neutral Gray FIFO realization passes silicon, while the registered-target
overlay maps to five `RAMB36E1` cells, completes all 512 transfers, and sets the
audit monitor's sticky order error on every one of five runs. A smaller probe
then ran 10,000,000 values through the exact 46-bit wrapper, its raw inferred
RAM leaf, an ordinary-logic reference, and split 32-bit/14-bit block-RAM banks.
The wrapper and raw 46-bit leaf failed with payload bit 44 inverted; ordinary
logic and both split banks passed. Thus Loom's registered presentation logic is
not at fault. The failure is the openXC7 72-mode `RAMB36E1` inference/lowering
selected for widths above 36 bits.

This suggests a narrow target-tooling request, not a core multiclock change.
Target leaves should carry qualification scoped by device family, toolchain,
primitive mode, width, and clock relationship. An openXC7 Zynq-7000 profile
should either reject this greater-than-36-bit dual-clock inference or bank the
payload into independently qualified widths. “The expected primitive was
inferred” must remain a synthesis fact, not be presented as proof of the
physical storage contract. Loom's named external assumption and physical
metadata already establish the right fail-closed seam; the next improvement is
backend-aware selection or rejection at that seam.

When reviewing this feedback file, the useful decision filter is:

1. Was application hardware expressible in Loom, or did missing semantics force
   handwritten RTL? In this work, application hardware remained expressible.
2. Is the issue generic semantics, a target-adapter contract, evidence tooling,
   or external campaign orchestration? Keep fixes at the narrowest boundary.
3. Did a symptom confuse a reasonable user even when the implementation was
   technically behaving as specified? Recovery observation is such a
   documentation/transport issue.
4. Does a target claim say exactly what was proved—simulation, inference,
   routing, or silicon—and name the toolchain/device scope?

The concrete requests justified now are fail-closed target qualification for
storage modes and backend-aware width banking. Recovery waveform metadata has
already landed; a sticky observation adapter remains optional transport
convenience. Vendor JTAG, board shells, constraints, and campaign policy should
remain outside Loom's core language.
