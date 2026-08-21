# Project status

Checked against repository head on **2026-08-20**. This file is a current
snapshot, not a development diary. Historical milestones belong in Git and
[`CHANGELOG.md`](CHANGELOG.md); detailed hardware campaigns belong in their
machine and board specifications.

## Gate status

| Check | Current result | Notes |
|---|---|---|
| `lake build` | **PASS** | Rechecked on 2026-08-20; the complete 8,337-job build passed with existing warnings. |
| `lake exe audit` | **PASS** | Rechecked on 2026-08-20; reports 36 inventoried unsafe declarations, 9 reviewed `implemented_by` replacements, 0 source `partial`, and 0 `extern`. The import replacements memoize transparent lowering/read checks by pointer identity; the Kahn-order proposal is accepted only by its transparent structural checker. |
| `lake test` | **PASS** | Rechecked on 2026-08-20; the complete 8,295-job graph passed, including the hierarchy package import regressions. |
| `scripts/quality.sh` | **PASS** | Rechecked on 2026-08-20, including the no-handwritten-certified-CDC gate. |
| `lake exe releaseAudit` | **PASS** | Rechecked on 2026-08-12 under a 24 GiB/no-swap cgroup; the combined and standalone multiclock release theorems have exactly `propext`, `Classical.choice`, and `Quot.sound`. Peak resident memory was 21.4 GiB. |
| certified multiclock emission | **PASS** | Re-emitted byte-identically on 2026-08-12; Icarus accepted `rtl/certified_multiclock/system.v` as a syntax/elaboration smoke check. |
| `scripts/emit_all.sh --check` | **PASS** | Rechecked on 2026-08-17; all 27 emitted artifacts matched a fresh emission. |
| `scripts/ci.sh` | **PASS** | Rechecked on 2026-08-09, including the explicit 528-second Epoch BMC, audit, emissions, debug map, round trip, release binding, and LRAT cross-check. |
| `scripts/reproduce.sh` | **NOT RECHECKED** | The broader reproduction wrapper remains a separate unrerun gate; optional external checks are host-dependent. |
| `scripts/build_verified_release.sh` | **NOT RECHECKED** | No current release rebuild is claimed by this snapshot. |
| Optional Yosys/CaDiCaL/Icarus checks | **Host-dependent** | Scripts self-skip when tools are missing. A zero exit from a wrapper does not by itself prove every optional check executed. |

`Machines.Epoch.Bmc` is an explicit CI target rather than part of the default
`Machines` umbrella. This keeps ordinary builds lightweight without dropping
the bounded-model-check proof from the standing gate.

The full reproduction and release workflows remain separate, explicitly
unrerun gates.

### RTL import status

The module-preserving import path is fail-closed and technology-neutral after
the external frontend boundary. Its current combinational vocabulary includes
bitwise and arithmetic operations, logical truth conversion, AND/OR
reductions, equality/ordering comparisons, and frontend-normalized priority
mux trees. First-class stateless components emit without synthetic clock/reset
ports and bind into any typed domain without acquiring state. Focused
original-vs-emitted sequential and combinational equivalence fixtures pass.

Schema-v2 closed hierarchy packages now carry exact child-input expressions
and unique child-output nets in a shared expression-DAG encoding. The trusted
checker validates every child and input binding, width/direction, driver,
module-instantiation DAG, and exact bottom-up combinational dependency cycle.
Checked structural wrapper/body emission handles both stateless and stateful
children; both original-vs-emitted hierarchy equivalence fixtures pass.
Single-module emission refuses hierarchical modules instead of leaving child
nets dangling.

Four-state constants now have an explicit implementation-refinement path.
Hash-bound policies classify stable sites and select zero/one only for unknown
bits; the trusted checker proves the concrete value preserves every known bit.
Unclassified or ambiguous sites fail closed, and the equivalence adapter can
apply the same named concretization to both original and emitted RTL. Unsigned
`$shiftx` variable part-selects use the same explicit partial-fill policy and
normalize to ordinary shifts/muxes; every KianV occurrence is unsigned. This
is now applied through a reviewed, exact-site KianV policy.

For the exact checked-in KianV elaboration, the policy-free baseline accepts
42 of 74 modules. The reviewed 32-decision/279-site four-state refinement and
checked mixed-edge package splitting raise acceptance to all 74 modules.
Child-instance binding, unsigned `$shiftx`, resetless state, nonuniform
per-register synchronous resets, ROMs, the six writable-memory modules, and
the falling/rising-edge SDRAM controller are no longer import blockers.
Writable `$mem_v2` cells are lowered into ordinary Loom word memories while
remaining exact: every whole-word port value folds earlier enabled
same-address bit masks, and only provably distinct literal-address writes are
commuted/grouped. The neutral artifact records exact original-to-Loom memory
and register correspondences for external equivalence. A multi-edge source module emits one
stateless combinational body plus one state-owning body for each clock/edge
domain; the checked wrapper binds their state nets explicitly and retains
clock pins used by combinational source cones.
[`Evidence/KianV/import_coverage.md`](Evidence/KianV/import_coverage.md) and
[`Evidence/KianV/import_coverage_policy.md`](Evidence/KianV/import_coverage_policy.md)
are the generated baseline and policy-dependent reports. Acceptance is not
equivalence or signoff. The complete 74-module package passes trusted
structural checking. The hash-bound compositional equivalence runner currently
proves all 73 Loom-logic specializations and records the GF180 SRAM wrapper as
the sole exact external contract. The logarithm hierarchy uses an explicit
flatten fallback; the other 72 proofs are compositional. The CPU, `soc`, and
whole `chip_core` boundaries pass. Four memory-bearing modules use exact packed
state relations plus zero-refinement base and one-step unbounded temporal
induction. The formerly open five-bank associative cache passes all 160 word
relations (2,016 state bits), so bottom-up conversion equivalence is closed.
[`Evidence/KianV/equivalence.md`](Evidence/KianV/equivalence.md) and JSON bind
the 74/74 result to the exact elaboration, package, emitted RTL, and GF180 SRAM
contract. Import lowering
memoizes the complete neutral expression-root batch, validates reads on that
compact source DAG, and uses an iterative postorder executable traversal so
deep generated cones do not retain recursive dependent-monad continuations.
Package topology removes processed modules by their already-unique names
instead of comparing their complete expression DAGs. The formerly failing
two-module TLB cache package now emits in 0.13 seconds at about 144 MiB peak
RSS; the complete 74-module/150-artifact `chip_core` package emits in 0.67
seconds at about 241 MiB peak RSS and passes an Icarus syntax/elaboration smoke
check. Complete package emission is no longer an open gate.
Safe, unique source module and instance identifiers are now retained in the
emitted hierarchy, with injective encoding reserved for parameterized or
otherwise non-portable Yosys names. The GF180 physical handoff restores the
54-pad integration parameter, real SRAM primitive, conditional power-pin tree,
and translated fixed placements. Its post-Yosys gate requires exactly 21 SRAM
primitive paths and binds the result in a deterministic manifest before the
pinned LibreLane flow may start. The handoff disables only Yosys's optional
SAT-based resource-sharing optimization, which is pathological for the
explicit TLB memory-read form; normal memory lowering and technology mapping
remain enabled. The first complete physical run reached final DRC/LVS and
exposed one SRAM-edge M3.2b site plus two marginal foundry-deck Metal2 antenna
markers. The handoff now enables a one-GCell macro routing extension and the
pinned heuristic diode stage at threshold 130; a clean rerun is the release
gate.
The separately hash-bound `SIM SYNTHESIS` elaboration of the emitted `soc`
boots the pinned KianV xv6 image through the existing pin-level
SDRAM/SPI/UART Verilator harness and reaches its shell at 222,410,634 clocks,
exactly matching the upstream run. `scripts/boot_kianv_xv6.sh` reproduces the
package, cleanup, build, and marker checks. This is end-to-end dynamic evidence,
complementing the now-complete bottom-up formal result.

### Multiclock execution-projection gate

Focused validation on 2026-08-16 passed for `Tests.SystemProjection`,
`Tests.SiblingProjection`, `Tests.ProjectionProgress`, and the fail-closed
`Tests.ProjectionAxioms`
audit. The result transports valid finite
reset-aware executions, state-dependent observed inputs, fragment island and
internal-channel state, time, clocks, and resets. It lifts one fragment-wide
FIFO ordering/no-loss theorem and one predicate-conditioned bounded-response
demonstration into two different parents. The latter states request
presentation, destination readiness, required fragment ticks, and reset
absence explicitly while permitting arbitrary irrelevant interleavings. The
standard include-and-close projection is derived from checked finite inventory
evidence. Builder-generated placements now give two sibling fragments
projections in either assembly order while preserving exact lookup and input
dispatch; duplicate inventory fails closed. A manual certificate remains
available for transformed adapters.
Its exact axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`.

The current composition closeout also provides an exact ordered
`CertifiedIslands.Inventory`. Including a `SystemFragment` appends its cached
child compiler/DAG certificates without recomputing them; the parent checks
only local islands and its structural channel/reset realization. The generic
`System.BuiltSystem` package is now the common checked assembly and emission
result, including the Typed SoC Composition Tile path.

System-level combinational observations are fail-closed declaration data.
Pretty `output wire` declarations become explicit observations, while internal
combinational nodes remain private; missing signals, kind/width mismatches, and
duplicate exports are rejected before realization. Contract-bound whole-island
substitution is available as a separate optional release layer. It retains the
certified reference `Design` for semantics and proofs, replaces only the exact
named emitted module, and records external bytes, evidence classification, and
named assumptions. External RTL equivalence remains an explicit premise.
The Typed SoC Composition Tile now exercises that path for its contracted
memory island. Loom emits the target-selected RTL and `external_islands.md`;
the former shell `sed` rewrite is gone. The physical RTL remains byte-identical
at SHA-256 `84fc8bf3…ea81c`, so its retained route and silicon evidence remain
about the exact current physical bytes.

`Loom/Hw/Chan.lean` and `Loom/Hw/System.lean` provide typed bounded-channel
handles, generated endpoints, synchronous FIFO lowering, named island
assembly, explicit co-tick policy, replayable named-clock events, abstract
multi-clock execution, derived crossing inventories, per-event framing, and
one-call lifting of ordinary open-Design invariants for every schedule.
Relational properties over the complete channel store have their own
`ChannelInvariant.and` and `System.liftChannels` composition/lifting path. The
checked abstract queue proves FIFO-head delivery and capacity preservation;
its finite-trace conservation theorem proves ordered losslessness, and a full
circular-buffer simulation proves the generated synchronous `Design` adapter
equivalent for every finite event trace. Regressions exercise both co-tick
policies and a two-clock transfer.

The implementation choice is not stored in `Chan`. `Chan.Refinement` is the
common proof interface for physical implementations; the actual generated
synchronous adapter, an adversarial-delay toggle mailbox, and an
adversarial-pointer-view asynchronous FIFO each satisfy it and inherit its
all-traces conservation theorem. `RealizedSystem` separately requires one
ordered physical binding per abstract connection. Its structural emitter
produces island RTL, generated top-level wiring, and readable crossing and
physical-intent reports; automation consumes the underlying typed values.
Checked theorems establish that the exact structured
channel instances and constraint groups consumed by the renderers cover the
declared connection list; the path also reuses every ordinary island emission
check before writing. An unrelated-clock Icarus smoke test compiles the
generated top and exercises one idealized payload transfer; this establishes
syntax/elaboration and a concrete wiring execution only, not refinement.

`CertifiedSystem` now packages a preparation-complete certified DAG simulator
for every island, reuses the exact `System` channel/input plan during replay,
and carries island agreement with the schedule semantics in every executable
state. It also requires a `Chan.Refinement` for every declared connection, so
certification cannot omit crossing behavior while certifying only endpoint
islands. Both the small and LNP64mini instances select the joined,
technology-neutral compiled-control/register-bank refinement. Its comparison
surface is derived from all island coordinates and all
bounded-channel slots; missing oracle coverage fails with coordinate names.
Each checked island also exposes its canonical UTF-8 artifact through
`CertifiedSystem.renderedIslandUTF8`, with a theorem reducing it to the
ordinary proved compiler and printer. `CertifiedSystem.runPrefix_semantic_eq`
also states explicitly that certified replay projects to the public System
runner on the identical schedule and input trace.
It is instantiated for both the small two-clock producer/consumer example and
a technology-neutral LNP64mini system whose real core publishes best-effort
retirement-PC telemetry to an independently clocked observer.

`Loom.Hw.Multiclock` now provides the ordinary application facade.
`ClockHandle`, `IslandHandle`, directional source/sink endpoints, and
`ChannelRoute` keep ordinary topology and inspection out of raw strings.
`SystemBuilder.addChannel` generates both endpoint adapters, and the checked
System calls `realizePortable` once; Loom derives
island certificates, stock FIFO controls and register-bank storage,
refinements, exact ordered artifact coverage, and clock rules.
`Application.run`, `readReg`, `readChannel`, and `emit` expose replay,
inspection, and certified output. `PackedChan` uses the same path while
preserving its semantic payload type through endpoints and hierarchical
exports, and `realizePortableChecked` reports
named readiness failures. Both the small
TwoClock example and the LNP64mini production consumer use this path and no
longer construct storage witnesses, lookup proofs, coverage proofs, or typed
DAG register views. Optional `system ... where` and `#run_system` syntax
remains a separate prettification concern.

`Application.runRecovery` and `runRecoveryChecked` extend the certified DAG
runner rather than exposing a second semantic evaluator. Their semantic
projection is proved equal to `System.runRecoveryPrefix` for arbitrary event
and input traces.

The asynchronous FIFO model now uses finite ring addresses rather than an
unbounded-memory surrogate. Lean proves that simultaneous successful read and
write ports address distinct physical slots, then discharges
`AsyncQueueStorage.CollisionFree`. A single parametric composition theorem
turns any implementation of that storage contract into a `Chan.Refinement`;
the compiler-produced portable register bank instantiates it at every supported
power-of-two depth without an external assumption. Its write- and read-domain
halves are ordinary `Design`s, and `AsyncQueueStorage.Portable.rep_step` proves
their actual `Design.cycleOpen` transitions implement the storage contract. The
result is joined directly to the parametric FIFO theorem in `Tests.Chan`; the
semantic reference register bank is no longer used as that non-vacuity witness.

Generic Loom now contains no handwritten behavioral CDC Verilog; a mechanical
quality gate enforces both that fact and the `Loom`/`Evidence` import boundary.
The former handwritten Gray FIFO renderer remains available only as explicitly
unverified integration evidence under `Evidence.ReferenceCdcRtl`. The certified
path now has ordinary write-domain and read-domain control Designs containing
the finite pointer registers, Gray increments, two-flop sampling chains, and
combinational full/empty comparisons. Both halves have `CertifiedDesign` packages and
cycle-level semantic equations. The executable FIFO model now also carries
both synchronizer stages explicitly, and the compiled write/read enable
expressions are proved equal to its accepted/delivered decisions under the
channel invariant. `AsyncFifoDesign.controlRep_step` proves the complete
compiled-control relation inductive for arbitrary source/sink tick sets,
adversarial samples, and held domains. `CertifiedPortableBinding` joins those
controls to proved compiled register-bank storage for arbitrary power-of-two
depths; `CertifiedSyncBinding` supplies the ordinary compiled FIFO for every
positive same-clock depth. `RealizationPlan` selects those leaves, including
the recovery-wrapped portable leaf, per typed route, and coverage requires
exactly one closed binding for every declared
connection. `CertifiedRealizedSystem` emits
only structural wiring around the compiler artifacts, and `verifiedReleases`
contains the literal emitted `system.v` artifact together with its exact UTF-8
equality and emission-list membership. Binary-reflected Gray adjacency is
machine-checked for ordinary
increments, finite-width bounds, and wraparound, and the executable FIFO's
read/write steps are proved to stutter or take such a transition. Metastability
and the physical old-or-new sampling argument remain outside the semantics.
The executable `independentFlush` recovery contract now states reset dominance,
incident-channel loss/flush, and nonincident preservation and has a reusable
capacity invariant. `Chan.RecoveryRefinement` additionally records the old
epoch discarded at a recovery completion. Its executable four-phase
request/acknowledgement protocol refines that contract under arbitrary clock
schedules, and the per-domain endpoint is a compiler-produced `Design` with a
proved cycle equation. `RealizationPlan.recoveryPortable` now joins compiled
endpoints and traffic/reset guards to the compiled portable FIFO, emits
per-island level request/completion ports, coordinates every incident channel,
and resets only the requesting island after both halves of every incident
channel complete. The exact coordinator domain is structured and has a
membership theorem. Policy/binding compatibility is a constructor proof, and
flattened parent/child reset-policy disagreement fails final System assembly.
FIFO halves remain reset throughout the endpoint `flushed` phase; the protocol
proves both completion edges saw reset asserted, closing the reset-skew hole
where an early half could sample the peer's old pointer. The RTL regression
checks every incident pointer and synchronizer is at the common empty origin
while recovery completion is asserted. A System theorem also lifts the exact
compiled endpoint reset-hold expression through the structured completion
domain, so coordinator completion machine-checkably covers every incident
half rather than relying on the smoke test.
The three-clock/two-channel RTL recovery regression passes. A coordinated
channel refinement now retains the logical old epoch when one physical FIFO
finishes early. The two actual compiled endpoint-controller states are proved
to follow that model, and the exact generated coordinator domain is proved to
commit both channels in the regression topology on the same
`System.advanceRecovery` event. The selected recovery binding's channel state
and loss accounting are joined at that event without a free alignment premise.
The remaining formal gap is the state relation carrying the compiled FIFO
controls, register-bank storage, and datapath guards through early local reset,
then packaging those facts as one whole-wrapper theorem. The exact compiled
island reset edge is already proved equal to the System island-reset action;
the passing unrelated-clock RTL recovery test remains smoke evidence. Checked `SealedBlock`s now package
typed open endpoints, cached island certificates, and dependent theorem
bundles; a parent can flatten blocks and close only endpoints indexed by the
same channel. Name collisions fail closed, while automatic namespace
prefixing of flattened instance-local names remains ergonomic follow-up.
Reusable `CertifiedIslands` values cache
large-island readiness across physical plans. Generated endpoint
`TransitionProperty` packages and board-wrapper adoption of the LNP64mini
System remain possible extensions;
they are not holes in the closed portable FIFO artifact described above.
See [`MULTICLOCK_BOUNDARY.md`](MULTICLOCK_BOUNDARY.md).

Selected channel timing is now inspectable as typed Application data or an
on-request human diagnostic. Normal emission has no CSV/TSV sidecars: it emits
readable `crossings.md` and `clock_constraints.md` reports, while tools consume
the typed inventory and timing values directly. Timing's
ordered connection coverage is proved complete. Stock descriptions include
both endpoint registers, synchronizer/storage stages, local source/sink issue intervals,
service premises, and recovery interruption. The async row honestly has no
finite end-to-end delivery bound under the current unbounded-staleness model.
The report also exposes endpoint performance. The compatibility sink consumes
once per two destination ticks. The opt-in buffered sink is destination-local,
contains no combinational CDC path, has conservation and steady-state
one-item-per-tick theorems, and reports a one-tick issue interval.

The portable binding also derives neutral physical intent for both exact
two-stage synchronizer chains and both Gray-pointer buses, including named
launch/capture objects and period-relative skew/datapath requirements. This is
substantially stronger than a clock-group-only report. Every distinct clock
domain also carries a typed reset-delivery contract matching the emitted
synchronous-reset RTL. Backend reports have exact ordered coverage of the full
timing-plus-reset requirement list and cannot silently omit an item. They bind
device, tool/version, run/seed, exact RTL/intent/target-constraint/routed
hashes, and post-synthesis name resolution; identity drift or missing objects
makes `passed` false. A small reference backend exercises coverage without
claiming signoff. The optional
openXC7 adapter consumes routed structural evidence but honestly returns
`UNCONSTRAINED` for unsupported clock-group and Gray-bus timing intent.

The portable storage contradiction is closed: its compiled reader is now
explicitly first-word-fall-through and combinational, with no reader registers,
rules, or unused `read_data`/`read_valid` ports. The wrapper consumes the same
`read_sample` expression used by the implementation refinement, and timing
reports zero storage-read stages. Registered-latency RAM/SRAM leaves remain a
separate substitution contract rather than a dormant second path.

## Formal verification state

- The LNP64-µ public ledger imports T1–T9, the machine invariant assembly, and
  R-MC from `Machines/Lnp64u/Theorems/Ledger.lean`.
- `lake exe audit` classifies all 1,061 ledger theorems as clean and finds no
  unapproved project axioms, no `native_decide`/trusted-compiler dependency,
  and no disallowed `sorry` outside the permitted theorem/WIP policy.
- R-MC supplies an unbounded simulation from the LNP64-µ machine model to the
  reachable compiled EDSL transition system, including reset and all modeled
  retirement arms.
- The generic compiler/emission proof covers the EDSL-to-µVerilog module
  semantics. Open-design cycle semantics and input/output support also exist.
- The expression language, reference and optimized evaluators, compiler,
  concrete SSA certificates, parser, and printer support same-width modular
  multiplication. RTL uses the neutral `*` operator so downstream FPGA or
  ASIC tools remain free to infer an appropriate implementation. Typed
  `Expr.umulWide` and `Expr.smulWide` constructors retain all unsigned or
  two's-complement product bits by lowering through that proved primitive;
  abstract cost reporting preserves the operands' meaningful widths. Typed
  concatenation is available as `Expr.concat` / `++#` and lowers to the proved
  primitive algebra. Unsigned division and remainder are total (`a / 0 = 0`,
  `a % 0 = a`) and compile through explicit guards before neutral `/` and `%`
  operators, with the same evaluator and release-certificate coverage.
  LNP64mini uses direct generic multiplication
  for ordinary low-half `MUL`; its high-half `MULH`/`MULHU` instructions remain
  on the intentional iterative shift-add path.
- `Tools/VerifiedRelease.lean` defines the combined Acc8/LNP64-µ/portable
  multiclock release theorem. Its named LNP64-µ consequences are authority
  confinement, machine-wide W^X, lineage-ledger conservation, and budget
  boundedness; its System leg carries the exact emitted RTL member and the
  small and production-scale certified-System instances.
- `Tools/ReleaseAudit.lean` requires the combined theorem's axiom closure to
  be exactly `propext`, `Classical.choice`, and `Quot.sound` when the release
  command builds it.

The release theorem is not a filesystem, synthesis, P&R, or silicon theorem.
See [`TCB.md`](TCB.md).

## Tool and artifact state

- Lean is pinned to 4.28.0; Mathlib and transitive dependencies are pinned by
  `lake-manifest.json`.
- The checked audit inventory currently contains 19 unsafe declarations and 5
  executable replacements. They are generator/tool performance paths; the
  release theorem is phrased over reference definitions and kernel-checked
  witnesses.
- The concrete release renderer and denotation cover registers, memory images
  and ordered writes, SSA wires, and outputs. Exact host-file association uses
  the separate binder described in `REPRODUCING.md`.
- There is currently no post-synthesis equivalence implementation in Loom. A
  future checker is scoped to a technology-neutral logical netlist; synthesis
  formats, vendor primitives, mapped netlists, and their conversion remain
  external evidence.
- Memory-target diagnostics are parameterized by explicit profiles from the
  separate `Evidence` library; they predict realizability but do not prove a
  synthesis mapping. Generic RTL emission selects no target.
- The primary LNP64mini simulator is generated from `Design`, prepares the
  certified shared DAG fail-closed, and drives its behavioral environment from
  generated core state. That environment now resolves typed register handles
  once into flat-state slots; missing or stale-width handles fail preparation,
  and generic slot-read theorems connect the resulting values to `Agree`.
  LNP64mini's hand-written cycle ISS, state adapter, and lockstep surface have
  been removed. Architectural tests consume typed `DerivedRun` observations;
  generated RTL matrices carry expectations produced by the proved simulator.
- LNP64mini's GP master, HP master, and HP arbiter now declare their inputs and
  state through typed handles. Their executable expressions, environment
  adapters, and outcome checks reuse those handles instead of repeating
  coordinate names and widths. Their duplicate ISS transition functions are
  gone; directed tests now assert handshake, routing, and reservation outcomes
  on the Design semantics.
- Open-machine environment adapters use heterogeneous typed `InputBinding`s;
  LNP64mini core/components and Substrate S0 no longer dispatch inputs through
  repeated string/width match tables. The core smoke battery checks seven
  architectural scenarios on the certified Design-derived simulator.
- LNP64mini's domain, fail-stop, data-cache, SMP, slot-capacity, MMU,
  subword, ALU-gap, gate, preemption, MMU-identity, and refusal-conformance
  gate-hammer/dwell, fault/sentinel, capability-transfer, trace, and relocation
  campaigns now consume typed `DerivedRun` observations. Preemption also
  audits every observed thread switch through resolved register/memory slots.
  The mirror-only opcode differential and emulator-step diagnostics were
  retired; emitted RTL remains checked against Design-derived architectural
  expectations.
- Substrate S0 and S13 no longer maintain second transition functions. Their
  tests use the universally related generated evaluators and check direct
  architectural outcomes through 100,008 S13 cycles and the complete
  33-command S0 trace. S0's command adapter derives input names from typed
  handles.
- `Loom.Runner` supplies the shared differential-run control and structured
  result contract used by Acc8, LNP64mini core/components, and FastEval
  corroboration. Acc8's bespoke comparator/recursive runner and LNP64mini's
  parallel evaluator entry points are gone; closed coverage gaps fail by name.
- `Loom.Artifact` binds observations to exact bytes and writes deterministic
  text only when bytes change. Generic shell helpers cover command capture and
  freshness; external workflows can create and verify SHA-256 identity
  manifests with `scripts/artifact_identity.py`.
- LNP64mini's generated debug map and core share a lightweight typed interface
  for observed registers, so the runtime generator stays cheap without
  redeclaring debug names and widths. Board transport remains external.
- Loom provides footprint-inferred `ExprProperty` state properties and general
  typed `TransitionProperty` before/after relations. LNP64mini proves with the
  latter that waking a parked thread preserves its ordinary resume PC and gate
  continuation metadata for every slot and stack depth.
- Runner mismatch output is flushed immediately. `emit_all.sh` uses the shared
  diagnostic helper, reports the exact failed command and output, and attaches
  a digest of the emitted artifact set to its successful result.

## Hardware integration

The current integration head is **hardware-green as external evidence** on one
accounted dual-core bitstream (`e66d2c22…`, unchanged across the compiler fix —
a new guest does not require a new FPGA implementation):

- the generic 64-bit `MUL` executes in the kernel; the stock-openXC7 `-nodsp`
  build routes at 55% LUT (59,035/106,400), ~32.86 MHz `sysclk`. DSP48 inference
  is an optional future flow (openXC7 0.8.2 wrongly rejects a legal unused
  terminal `PCOUT`), not part of this result;
- the sentinel gate ABI runs the §17 write-gate handler as an ordinary C
  function.

### Accepted network path: native GEM0, JTAG-free, dual-core SMP

The mission network path is **native GEM0**: both fabric cores run one NetBSD
kernel (`LNP64_SMP` + two rump vCPUs), driving the PS GEM0 MAC directly over the
GP aperture; JTAG loads the image and then EXITS. `e2e.sh` proves it fail-closed
on silicon with the **servicer stopped (`xsdb=0`, A9 halted)**:

- boot → DOMAINS → **core 1 running** — the `CORE1: started` line is parsed and
  required to match the nm-derived entry, `status=0x1`, retirement above a
  worker threshold, and no core-1 fault;
- **ping 4/4** over real Ethernet (~300 ms);
- **telnet** `uname` + gated `echo`, each reply byte crossing the §17 write gate;
- **`cpus` → `ncpuonline=2`** answered over the network with the JTAG stack dead
  — a guest-visible two-CPU proof that depends on no BSCAN read.

No JTAG, no A9, no host bridge in the packet path. The legacy shmif-over-JTAG-ring
path (`ring_pump.tcl` / `shmif_bridge.py`) is debug-only (`board/LEGACY.md`).

Every image-specific address — the §17 gate/cap table roots **and** the core-1
entry — is `nm`-derived at build time into `mini_domains.env` (deployed beside
the hex, sourced by the boot), so no maintained boot carries a hardcoded
per-build address. The tp-reserved (fixed) clang (psABI §1 / ISA §2269) is
vindicated: the gated telnet reply works, so there is no gated-write regression.

## Property limits that remain open

- T5 erases timing through destuttering and is conditional on its isolation,
  agreement, code-locality, W^X-disjointness, and top-priority hypotheses.
- T6/T7 are conditional scheduler results, not global liveness under arbitrary
  memory stalls, interrupts, clock gating, or platform failures.
- The model is two-state and begins from a mathematical reset state.
- External DMA, interrupts, debug, MMU/IOMMU behavior outside a modeled
  machine, and hostile SoC agents are not silently included.
- Electrical reset, metastability physics, timing closure, power, analog
  effects, and physical side channels remain outside the core theorems.

The longer adversarial analysis is [`TRUST.md`](TRUST.md).

## Where to look next

- Release claim and TCB: [`TCB.md`](TCB.md)
- Independent reproduction: [`REPRODUCING.md`](REPRODUCING.md)
- Ordered unfinished work: [`ROADMAP.md`](ROADMAP.md)
- Hardware record: [`fpga/zc702/README.md`](fpga/zc702/README.md) and the
  specifications below each `Machines/` subtree
