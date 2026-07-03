import Loom.Emit.MicroVerilog.Semantics

/-!
# The single trust axiom (L4)

The one axiom in the whole stack (TCB item 2). It is imported *only* by
emission-dependent theorems; the audit tool whitelists it there and
flags it anywhere else.

Informal reading: any conforming Verilog tool (simulator, synthesizer,
place-and-route, ASIC flow) implements, on the µVerilog subset, the
synchronous transition-system semantics `Module.cycle`/`Module.reset` of
`Semantics.lean`. This is the assumption every trusted-pretty-printer
design makes silently; here it is stated, minimized by the subset's
austerity, and corroborated per target by lockstep and the conformance
suite (never proven — that is the honest boundary). One point the reading
leans on explicitly: a memory's write ports are printed as successive
guarded nonblocking assignments to the same array in one
`always @(posedge clk)` block, and IEEE 1800 prescribes last-update-wins
for multiple nonblocking updates to the same variable in the same time
step — exactly `Module.cycle`'s in-order port commit.

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

/-- The boundary axiom, as a *predicate* a target discharges by
corroboration (never by proof): the tool's realization agrees with the
formalized µVerilog semantics on `m`. -/
axiom ImplementsStandard {m : Module} (t : ToolRealization m) : Prop

/-- The axiom's content: `ImplementsStandard` holding means the tool's
reset and cycle *are* the semantics. Stated as an axiom because it relates
the opaque predicate to the (physical) tool — this is the single trust
assumption. -/
axiom implements_standard_spec {m : Module} (t : ToolRealization m) :
    ImplementsStandard t → t.reset = m.reset ∧ ∀ σ, t.cycle σ = m.cycle σ

end Loom.Emit.MicroVerilog
