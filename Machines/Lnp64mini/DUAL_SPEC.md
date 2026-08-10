# Dual-core LNP64mini

`DualSoc.lean` composes two LNP64mini cores with `HpArbiter.lean` and the
shared SoC interfaces. It is the repository's bounded SMP implementation,
not a claim of a complete LNP64 platform.

## Memory and atomicity

Both cores share the HP memory path. The arbiter serializes requests and owns
the global LR/SC reservation, so stores and successful conditional stores are
ordered at that point. Core-local state remains independent. The model is a
small, serialized memory system; it is not a cache-coherent weak-memory
implementation.

Core 1 can be held at reset/release through the wrapper-facing control. The
debug DDR window is also arbitrated explicitly. GP transactions complete
through the supported aperture instead of being silently treated as shared
HP traffic.

## Storage shape

Large per-thread structures use Loom memories rather than flattened register
arrays. Read timing follows the D19 discipline where synchronous memory is
required, and write-port behavior follows Loom's ordered commit semantics.
Bulk table reset that cannot be delivered as a physical initialization image
must use an explicit runtime sweep or a target that supports the image.

## Verification

The maintained checks are Design-derived core and arbiter selftests,
emitted-RTL simulation against Design-derived expectations, memory target
checks, and the configured post-synthesis flow. The wrapper and external
DDR/PS behavior are separate from the Loom module claim.

The present board head is green as external evidence: one accounted dual-core
artifact boots NetBSD, completes ping 4/4, returns `uname` and echo traffic
through gate 1/domain 1, and runs the shmif driver through the domain-2 path.
The accepted implementation uses LUT-mapped direct multiplication. This does
not strengthen the Loom theorem boundary; `STATUS.md` is the operational
record.

## Boundary

The design does not provide cache coherence, speculative execution, a general
IOMMU, or the full architecture profile. It also does not turn a board test
into a proof of the PS7, DDR controller, clocking, CDC, or place-and-route.
