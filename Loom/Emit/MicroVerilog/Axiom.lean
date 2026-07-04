-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Emit.MicroVerilog.Semantics

/-!
# The µVerilog tool-boundary assumption (L4)

The one non-kernel boundary assumption in the stack (TCB item 2), exposed
as two Lean axiom declarations: the opaque predicate
`ImplementsStandard`, and the eliminator `implements_standard_spec` that
connects that predicate to the formal transition semantics. They are
imported *only* by emission-dependent theorems; the audit tool whitelists
exactly these declarations and flags any other project axiom.

Informal reading: for a specific emitted µVerilog module `m`, a specific
observed tool realization `t` has the reset state and one-cycle transition
given by `Module.reset m` and `Module.cycle m`. This is not a claim about
the whole Verilog language, timing closure, power, glitches, metastability,
or arbitrary downstream flows; those are outside the formal boundary. The
assumption is minimized by the subset's austerity and corroborated per
target by lockstep and conformance runs (never proven — that is the honest
boundary). One point the reading leans on explicitly: a memory's write
ports are printed as successive guarded nonblocking assignments to the same
array in one `always @(posedge clk)` block, and IEEE 1800 prescribes
last-update-wins for multiple nonblocking updates to the same variable in
the same time step — exactly `Module.cycle`'s in-order port commit.

Formally we phrase it as an opaque predicate `ImplementsStandard tool m`
asserting a tool's observed cycle behavior on module `m` equals
`Module.cycle m`. Theorems that reach past the boundary carry
`ImplementsStandard` as an explicit hypothesis, so the axiom appears in
their statement's fine print rather than being assumed globally.
-/

namespace Loom.Emit.MicroVerilog

/-- Abstract handle for a downstream tool's realization of a module: its
reset state and its one-cycle transition, as the tool actually computes
them on hardware/in simulation. -/
structure ToolRealization (m : Module) where
  reset : St
  cycle : St → St

/-- The boundary predicate: a target-specific claim, discharged only by
external corroboration, that this tool realization is intended to implement
the formalized µVerilog semantics on `m`. The semantic content is exposed
only by `implements_standard_spec`. -/
axiom ImplementsStandard {m : Module} (t : ToolRealization m) : Prop

/-- The boundary assumption's content: `ImplementsStandard` holding means
the realization's reset and cycle are exactly the formal semantics. Stated
as an axiom because it relates the opaque predicate to an external tool
observation. -/
axiom implements_standard_spec {m : Module} (t : ToolRealization m) :
    ImplementsStandard t → t.reset = m.reset ∧ ∀ σ, t.cycle σ = m.cycle σ

end Loom.Emit.MicroVerilog
