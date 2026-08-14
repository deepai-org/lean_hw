# Pretty Loom usability issues

This file records confusing or inefficient user-facing behavior encountered
while using the pretty syntax. An entry does not have to establish a compiler
bug: misleading diagnostics, surprising name resolution, or a missing natural
spelling are issues for a user-friendliness layer.

## Reusing an endpoint-adapted island duplicates its adapters

**Status (2026-08-14): partially addressed.** `SystemBuilder.check` now
recognizes duplicated stock maintenance rules and reports adapter duplication,
the likely already-adapted island, and the two valid repairs. It no longer
misdiagnoses this case as application arbitration. Pretty `system` declarations
still intentionally generate their own endpoints; exact reuse of an
artifact-bound adapted island remains an expert `SystemBuilder.connect` path.

In a pretty `system`, the natural spelling

```lean
island cpu on cpu_fabric_clk := Machines.Multiclock.SoCFabricGauntlet.cpu
```

accepts an existing `Design`, but `SystemBuilder.addChannel` later applies
source/sink adapters again. The standalone generated `recoveryFabric.cpu`
still has the supplied six rules and reports two writes to
`__loom_chan_cpu_request_src_valid`; the copy stored in the generated builder
has duplicated endpoint-maintenance rules, reports three writes, and fails
with:

```text
channel cpu_request: multiple sends may execute in one source tick; select one payload or use an explicit arbiter
```

That diagnostic points at application arbitration even though the supplied
application has only one send site. The pretty surface needs either a natural
way to declare an already-adapted island/connection, an early diagnostic that
the supplied design already contains the generated endpoints, or wording that
identifies adapter duplication. This matters for preserving an existing
multi-route `System` whose adapter nesting is intentionally artifact-bound.

## Atomic supplied-design names ignore an opened namespace

**Status (2026-08-14): resolved.** The command elaborator now resolves atomic
supplied Designs before generating nested declarations. Ordinary opened-
namespace lookup works, while an outer declaration with the same short name as
the generated island remains protected from capture. Both cases have focused
regressions.

With `open Machines.Multiclock.SoCFabricGauntlet`, writing

```lean
island cpu on cpu_fabric_clk := cpu
```

looks like ordinary Lean name resolution, but the system elaborator rewrites
the atomic name into the current namespace and reports an unknown local
constant. Fully qualifying the design works. Either ordinary opened-namespace
resolution should be honored or the diagnostic/documentation should explain
that supplied atomic design names are resolved relative to the current
namespace.

## Target-storage substitution drops below the pretty surface

**Status (2026-08-14): resolved without target syntax.**
`System.CertifiedBindingOverlay` accepts a sparse list of replacement bindings,
checks that each names an existing canonical connection exactly once, and
derives ordered coverage for the resulting artifact. Evidence code now writes
only its target-specific replacements and calls `artifact.withOverlay`; the
technology-neutral `system` declaration and stock realization profile remain
unchanged.

The pretty `system` syntax is effective for declaring the technology-neutral
topology and selecting Loom's stock synchronous, Gray-FIFO, or recoverable
realizations. There is no corresponding friendly spelling for retaining that
exact `System` while replacing selected portable bindings with a certified
target-storage leaf. The storage-neutrality experiment therefore constructs
the replacement `CertifiedChannelBinding` list in ordinary Lean.

Keeping vendor-specific storage declarations out of the technology-neutral
`system` block is a sensible scope boundary, so this is not necessarily a
request for a new core clause. It is still a user-facing rough edge: the jump
from

```lean
realize dma_request with Cdc.grayFifo
```

to manually rebuilding a heterogeneous certified binding inventory is large.
A small target-realization overlay or helper that says “replace this connection
with this checked physical leaf” would preserve the separation while making
the supported workflow discoverable.
