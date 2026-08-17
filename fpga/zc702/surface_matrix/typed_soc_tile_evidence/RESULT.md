# Typed SoC Composition Tile — ZC702 evidence

Date: 2026-08-17
Board: ZC702, XC7Z020
Result: **PASS**, with openXC7 CDC/timing-constraint coverage explicitly partial

## Certified construction

The release path executes the exact fail-closed `SystemBuilder.assemble`,
island-readiness, fragment-realization, parent-closure, and selected-channel
checks. Successful dependent branches package a `CertifiedRealizedSystem`; an
error branch cannot return an artifact. This avoids `native_decide` over the
large flattened component graph while retaining checked `SystemFragment`
interfaces through parent closure.

The enforcing axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for `coreGraph`, `buildTileFragment`, `monitorFragment`, and
`buildCertifiedArtifact`. The emitted neutral RTL SHA-256 is:

`01b8b73616c9ed5ee8b21e0f31bcc30c46d2585f9a51c4340b247f388f674536`

The target evidence layer changes exactly the `contract_memory` declaration
to request a 512x32 single-clock Xilinx block RAM. The resulting physical RTL
SHA-256 is:

`84fc8bf3c1cf85e313e6a66016557307af4ee4ea7c2cd28eeed804ddfd4ea81c`

The internal lane remains ordinary Loom-generated memory. Neither memory is
dual-clock; all cross-domain traffic uses the four certified depth-8 channels.

## RTL campaign

The target-selected RTL passed one million source transactions with unrelated
10 ns and 14 ns simulation clocks, periodic coincident edges, producer,
pipeline, memory and response pauses, an occupied pipeline flush, and common
reset with traffic resident:

```text
TYPED_SOC_TILE_PASS records=999999 digest=00000022 request_stalls=31/42 response_stalls=0/174058 pair_skew=838612
```

The checker verifies both memory responses, exact per-client sequence,
payload, masked-write semantics, arbitration and endpoint ledgers, the one
discarded request, and a rolling digest.

## Route and implementation

openXC7 0.8.2 / Yosys 0.38, seed 9, routed the exact physical RTL and wrapper.
The core clock is a continuously running divide-by-four of the independent
200 MHz board clock; the memory clock is PS FCLK0 at 100 MHz. Only BUFGCE gates
the clocks for coordinated reset release.

- 4,060 / 106,400 `SLICE_LUTX`
- 2 / 280 `RAMB18E1`; 0 `RAMB36E1`
- 4 / 32 `BUFGCTRL`
- final routed core Fmax: 79.31 MHz; applied clock: 50 MHz
- final routed memory Fmax: 133.00 MHz; applied clock: 100 MHz
- final routed 200 MHz root Fmax: 357.91 MHz; applied clock: 200 MHz
- final routed BSCAN TCK Fmax: 121.07 MHz

The backend prints `PASS at 12.00 MHz` because its reduced XDC cannot resolve
the generated PS7/BUFG/BSCAN clock objects. Therefore those printed PASS labels
are not used as signoff. The comparison above uses the backend's routed Fmax
against the known hardware clock rates. The full authoritative XDC is
`typed_soc_tile.xdc`.

## CDC coverage

The checked-System report contains exactly four asynchronous crossings:

- two 66-bit request channels, core to memory;
- two 62-bit response channels, memory to core;
- depth 8 and exchange co-tick policy for every channel;
- eight named two-stage Gray-pointer synchronizer chains; and
- eight four-bit Gray-bus skew/max-delay intents.

The emitted inventory and physical-intent report cover every declared channel.
The openXC7 route does not consume the generated-clock, asynchronous-clock
group, `ASYNC_REG`, or Gray-bus constraints, so this run is **not** presented as
a vendor CDC-report PASS. Silicon plus the exact structural inventory is the
available physical corroboration; a Vivado `report_cdc` remains unavailable
because this installation lacks Zynq-7000 device support.

## Silicon campaign

The exact seed-9 bitstream was identified through BSCAN by the physical RTL
hash prefix and passed:

```text
TYPED_SOC_TILE_SILICON_PASS transfers=1000000 records=999999 digest=00000000 gap=00100000
```

The setup first holds the memory services until the request crossings are
backpressured, then releases memory while holding monitor consumption until
responses are resident. Before asserting reset, the campaign requires the
endpoint-send ledger to exceed each lane's commit ledger and each lane's
commit ledger to exceed the checker record ledger. Those strict inequalities
prove that requests and responses are simultaneously resident at both
crossings instead of relying on a generic activity bit. It asserts only Loom's
supported coordinated reset, with both clocks running, and verifies the clean
channel/register restart.

The pre-reset tags are read-only, so memory retention does not weaken the
post-reset oracle. The final run exercises every requested pause/backpressure
class, occupied flush, exact source/grant/send/commit/delivery counts, response
ordering and payload, both memory lanes, sticky error, and a host-replayed
expected digest computed from the exact discarded `(client, sequence)` exported
by hardware.
It also requires nonzero response-queue stalls in at least one memory service,
showing that checker backpressure propagated through a response crossing.

The route outputs are retained on the board host under
`/tmp/typed-soc-tile-final2.UwFcDr/out`; their identities are recorded in
`SHA256SUMS`. The checked-in source, hashes, and silicon transcript—not that
temporary directory—are the durable evidence boundary.
