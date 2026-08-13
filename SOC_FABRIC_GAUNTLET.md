# SoC Fabric Gauntlet

## Purpose

The SoC Fabric Gauntlet is the proposed second multiclock Loom stress test. It
must complement the existing Clock Gauntlet rather than repeat it at a larger
packet count.

The existing gauntlet establishes that a feed-forward transform stream remains
ordered and correct across unrelated clocks, arbitrary schedules,
backpressure, pauses, pointer wraparound, and reset campaigns. This gauntlet
asks the next SoC-shaped question:

> Can one small, realistic, bidirectional and contended subsystem be written
> once, verified compositionally, compiled to neutral RTL, and exercised under
> unrelated clocks without exposing CDC implementation machinery to its
> designer?

This remains a language, verifier, and compiler experiment. FPGA runs are
implementation evidence for the emitted artifact, not additions to Loom's
formal claim and not a requirement for building generic Loom.

## System under test

The system is a tagged transaction fabric connecting two initiators to one
small memory-mapped register service, with a separate audit stream:

```text
 CPU client ---- requests ----\
   clk_cpu                     \
        ^                       v
        \---- responses ---- Fabric ---- requests ---- Register service
                              clk_fab                   clk_mem
        /---- responses ----    ^                           |
        v                       /                           |
 DMA client ---- requests -----                            |
   clk_dma                                                  v
                                                    audit/telemetry
                                                        clk_mon
```

The fabric explicitly arbitrates between the clients. The register service
acts like a small memory-mapped peripheral or SRAM controller. The monitor
checks committed-transaction records without defining the functional behavior
of the register service.

This shape exercises properties absent from a linear stream:

- bidirectional request and response traffic;
- multiple initiators contending for one target;
- explicit arbitration in ordinary `Design` logic;
- association of responses with requesters and tags;
- backpressure at request, target, response, and telemetry boundaries;
- a mixture of same-clock and asynchronous routes;
- packed protocol records and masked partial updates;
- reset with transactions at different protocol stages; and
- an observational domain whose role is explicit.

## Deliberate scope limit

The first version contains:

- two clients;
- at most one outstanding request per client;
- one round-robin fabric arbiter;
- one ordered target;
- six functional request/response channels plus one audit channel;
- FIFO depth two or four;
- a 256 by 32-bit register service; and
- no target-specific primitive in the Loom design.

It does **not** add AXI compatibility, caches, coherence, speculative
execution, out-of-order responses, interrupt controllers, descriptor chains,
a software-running processor, or an ASIC tool requirement. Those would obscure
the language and verification questions this experiment is intended to answer.

## Packed transaction types

The protocol should use typed packed records rather than manually sliced flat
words. The exact Lean spelling may follow the packed/prettification work, but
the semantic payloads are:

```lean
structure Request where
  client : BitVec 1
  tag    : BitVec 4
  write  : BitVec 1
  addr   : BitVec 8
  data   : BitVec 32
  mask   : BitVec 4
  deriving HwPacked

structure Response where
  client : BitVec 1
  tag    : BitVec 4
  data   : BitVec 32
  error  : BitVec 1
  deriving HwPacked

structure CommitRecord where
  client : BitVec 1
  tag    : BitVec 4
  addr   : BitVec 8
  write  : BitVec 1
  result : BitVec 32
  deriving HwPacked
```

This makes the gauntlet exercise field selection, field updates, packing across
CDC, byte-masked writes, and proofs stated over meaningful records rather than
bit offsets. Packed layout must be derived once and checked against the emitted
widths.

## Clock and route plan

Use a mixed topology rather than making every connection asynchronous:

- CPU and fabric share a clock; their request and response routes select the
  synchronous realization.
- DMA uses an unrelated clock.
- The register service uses a second unrelated clock.
- The audit monitor uses a third unrelated clock.
- Unrelated clocks may have coincident edges under `ClockRel.asynchronous`.

One emitted system must therefore contain same-clock FIFOs, asynchronous
request and response FIFOs, a one-way audit FIFO, several packed widths, and
multiple independent synchronizer/Gray-bus requirement groups.

## Functional behavior

### Fabric

The fabric is ordinary synchronous hardware. It must:

1. Inspect the two request inputs.
2. Select no more than one request per fabric tick.
3. Use round-robin priority when both are available.
4. Forward a request only when the target route can accept it.
5. Retain the routing information required for its response.
6. Return the response to the originating client.
7. Stall safely if that client's response channel is full.

CDC transports data; the `Design` owns arbitration and routing policy. The
multiclock layer must not acquire a hidden many-to-one or arbitration semantic.

### Register service

The target implements reads and byte-masked writes:

```text
read:  response.data = memory[address]

write: update exactly the bytes selected by request.mask
       response.data = the resulting word
```

Every committed operation also produces one `CommitRecord`. For v1, make audit
delivery lossless so its backpressure is part of the explicit functional
contract. A future lossy debug/telemetry abstraction would be a different
channel contract and must not be approximated here.

## Verification obligations

### Unconditional safety

For every finite schedule admitted by the declared clock relation, prove:

- every response corresponds to exactly one accepted request;
- client and tag are preserved;
- no response is routed to the wrong client;
- no accepted request receives two responses;
- each client's response order matches its accepted-request order;
- the arbiter never forwards two requests in one fabric tick;
- target state equals application of the committed write trace;
- read responses match the abstract register-service model;
- masked writes change exactly the selected bytes;
- every channel remains within capacity;
- audit records are an ordered copy of committed operations;
- pauses and coincident unrelated edges preserve all safety properties; and
- the monitor cannot affect behavior except through the declared lossless
  backpressure path.

The intended top-level statements are equivalent to:

```lean
responses client events =
  modelResponses client (acceptedRequests events)

committedMemory events =
  applyWrites initialMemory (committedRequests events)
```

Safety must not depend on fairness, clock ratios, or a global cycle.

### Conditional progress

Under separately named premises that all required domains continue ticking,
clients eventually accept responses, the target eventually accepts requests,
the audit monitor eventually consumes, and arbitration continues, prove:

- every accepted request eventually receives a response;
- a continuously requesting client cannot starve;
- round-robin waiting is bounded in fabric grants; and
- after clients stop issuing, the system eventually drains.

Keep these assumptions out of the unconditional safety theorem.

### Compiler and artifact binding

The evidence boundary must bind the theorems and campaigns to:

- exact emitted island modules and top-level RTL;
- exact channel and crossing inventory;
- exact per-route synchronous/asynchronous realization choices;
- exact physical-intent requirement coverage;
- exact packed widths and field layout;
- exact reset contract; and
- the literal canonical `system.v` bytes selected by the emitter.

Negative fixtures must reject or detect swapped tag/client fields, a wrong
packed width, a missing response route, multiple same-tick endpoint uses, a
missing synchronizer stage, an uncovered Gray bus, a wrong endpoint clock,
byte-mask corruption, and an accidental undeclared dependency from telemetry
to functional progress.

## Executable and FPGA campaigns

All campaigns first run through certified schedule replay. FPGA execution then
corroborates the exact emitted artifact under physical clocks.

1. **Balanced traffic.** Both clients continuously mix reads and writes.
2. **DMA faster than fabric.** Sustain request backpressure and pointer wraps.
3. **CPU response stall.** Stop CPU response consumption while DMA continues.
4. **Register-service pause.** Fill request paths, stop the target clock,
   restart it, and drain exactly.
5. **Monitor pause.** Demonstrate the declared lossless audit backpressure.
6. **Coincident edges.** Choose unrelated frequencies whose edges periodically
   coincide.
7. **Arbitration pressure.** Keep both clients requesting and check the
   round-robin grant bound and exact per-client counts.
8. **Masked-write sweep.** Exercise all sixteen byte masks and compare against
   the on-chip reference model.
9. **Reset boundaries.** Trigger the declared reset behavior with requests at
   each protocol stage: client-held, request FIFO, arbiter-selected, target
   FIFO, committed-response-pending, and response FIFO.
10. **Corruption detection.** In separate negative builds, corrupt client, tag,
    mask, response data, RTL identity, and physical-intent coverage. Every
    corruption must produce the intended failure rather than a plausible PASS.

A long soak follows these campaigns, but transfer count is not itself the
claim. Each result must report which behaviors and boundary conditions were
actually exercised.

## Neutrality experiment

When target-refined storage exists, realize the exact same Loom `System` twice:

1. with fully neutral compiler-produced register storage; and
2. with an FPGA block-RAM leaf satisfying the same storage contract.

Require the same accepted-request/response semantics, transaction theorems,
packed layouts, and test vectors. The emitted physical leaf and its evidence
may differ; the source hardware and channel proofs must not. This experiment is
optional for the first gauntlet milestone and does not require an ASIC flow.

## Proposed repository layout

Source and proof material should use the same separation as the first Clock
Gauntlet:

```text
Machines/Multiclock/SoCFabricGauntlet/
  Design.lean
  Proofs.lean
  Execution.lean
  Bounded.lean
  Certification.lean
  Artifact.lean

Machines/Multiclock/SoCFabricGauntlet.lean
Tests/SoCFabricGauntlet.lean
Tools/SoCFabricGauntletCampaign.lean
Tools/SoCFabricGauntletEvidence.lean
Tools/SoCFabricGauntletAxiomAudit.lean
```

Canonical generated artifacts belong under:

```text
rtl/soc_fabric_gauntlet/
  system.v
  crossings.md
  physical_intent.md
  timing.md
  artifact-manifest.json
  SHA256SUMS
```

Only deterministic compiler products belong there. FPGA tool working
directories, caches, routed databases, and logs must not be mixed with the
canonical RTL.

## Result locations and required records

### Formal and executable result capsule

`Tools/SoCFabricGauntletEvidence.lean` should accept an output directory. The
standard local output is:

```text
build/soc-fabric-gauntlet/evidence/
  RESULT.md
  result.json
  theorem-axioms.txt
  artifact-manifest.json
  simulation-campaigns.json
  negative-campaigns.json
  physical-requirements.md
  SHA256SUMS
```

`build/` is disposable and normally untracked. A release or review capsule may
copy these exact files elsewhere, preserving their hashes.

### FPGA evidence

Target-specific evidence belongs beneath the target, not in generic Loom or
`Evidence/` Lean source modules:

```text
fpga/<target>/evidence/soc-fabric-gauntlet/
  RESULT.md
  result.json
  canonical-artifact.sha256
  backend-coverage.md
  implementation-summary.json
  timing-summary.txt
  cdc-summary.txt
  campaigns/
    balanced.json
    dma-faster.json
    cpu-response-stall.json
    service-pause.json
    monitor-pause.json
    coincident-edges.json
    arbitration-pressure.json
    masked-write-sweep.json
    reset-boundaries.json
    corruption-detection.json
  runs/
    <run-id>/
      manifest.json
      tool-versions.txt
      hashes.txt
      raw-log-index.txt
```

If the FPGA work runs in a separate checkout or hardware host, it must retain
this same relative `evidence/soc-fabric-gauntlet/` layout. Large raw tool
databases may remain outside version control, but `raw-log-index.txt` must name
their locations and hashes. The concise `RESULT.md`, structured `result.json`,
requirement coverage, tool versions, campaign results, and exact hashes are the
reviewable record.

### `RESULT.md` rules

The top-level result must distinguish these categories explicitly:

- **FORMAL:** theorem/build/axiom result;
- **EXECUTABLE:** certified replay and negative-campaign result;
- **ARTIFACT:** exact RTL and manifest identity;
- **BACKEND:** requirement-by-requirement `PASS`, `SKIP`, or `UNCONSTRAINED`;
- **FPGA:** synthesis, implementation, timing/CDC reports, and board campaigns;
  and
- **OVERALL:** the conjunction actually justified by the preceding categories.

A missing tool or unavailable board is `SKIP`, never `PASS`. An uncovered
required constraint is `UNCONSTRAINED`, not `SKIP`. FPGA evidence must identify
the literal `system.v` hash it exercised. Physical results remain evidence and
must not be described as proving Loom's semantic or compiler theorems.

## Completion criteria

The gauntlet is complete when:

1. the schedule-independent transaction and memory safety theorems close;
2. conditional arbitration/drain progress is proved under explicit premises;
3. the exact neutral RTL and physical-intent inventory are artifact-bound;
4. all executable positive and negative campaigns pass;
5. one FPGA target executes every applicable campaign against the exact
   canonical artifact with honest backend coverage; and
6. the final result preserves the boundary between formal proof and physical
   implementation evidence.
