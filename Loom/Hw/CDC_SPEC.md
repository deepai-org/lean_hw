# Clock-domain crossing contract

Loom models the control path that crosses from the FPGA debug clock domain
into `sysclk`. It does not model metastability physics.

## Wrapper crossings

The ZC702 wrappers contain three kinds of crossings:

- A debug `UPDATE` event latches command fields and flips a toggle. A
  synchronizer carries the toggle into `sysclk`, where an XOR produces a
  one-cycle command pulse.
- Read-back logic samples either quasi-static captured values or
  tear-tolerant liveness counters into the debug clock domain.
- Power-on-reset counters synchronize reset release.

The physical assumption is that the first synchronizer flop resolves to a
Boolean value before the next sampling edge. MTBF and implementation quality
below that assumption remain properties of the FPGA primitive, placement,
clocking, and board environment.

## Verified toggle model

`Loom/Hw/CdcContract.lean` represents a source event stream, the source
toggle, synchronizer state, and an adversarial resolution oracle. For events
spaced by at least four destination-clock cycles, `toggleSync_sound` proves:

- each event produces exactly one pulse, at latency two or three;
- every pulse is one cycle wide; and
- no pulse occurs without a source event.

The sharper `pulse_at_event` result states that the oracle chooses only which
of the two legal latency cycles contains the pulse.

`CmdPulseTrace k` is the downstream interface contract. It includes an
initial quiet period, pulse spacing, and stability of the command fields for
the full destination-clock cycle before each pulse. From `Spaced k` with
`k >= 4`, `toggleSync_cmdPulseTrace` establishes spacing `k - 1`; the weaker
`k - 3` form is also available as `toggleSync_cmdPulseTrace'`.

Design-level proofs may assume a `CmdPulseTrace` for wrapper-delivered
commands. They must not infer analog metastability behavior, atomic sampling
of tear-tolerant counters, or guarantees for events outside the spacing
contract.
