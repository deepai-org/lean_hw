# L3 — Hardware EDSL and verified compiler: design

**Named win (Rule 5):** exact fit to the `TSys` spine and the `View` construct —
rule-atomic semantics whose linearization points coincide with the spec's
instruction-retirement snapshots, and maintained views whose data structures *are* the
T2/T3/T9 induction hypotheses. No existing framework (Kôika, Bluespec, Chisel) gives us
that coupling, and none is importable under Rule 4 anyway.

## Semantics (from the Kôika papers; no Kôika code)

- A **design** is: a set of typed registers/memories, and an ordered list of **rules**.
- A **rule** is an atomic guarded action: reads observe the *pre-cycle* state; writes are
  accumulated in a log; a rule that double-writes or reads-after-write in conflict with an
  earlier rule in the schedule *aborts* (its writes drop) — the one-rule-at-a-time (ORAAT)
  semantics.
- **Cycle semantics** = fold the schedule over the log; commit the log at cycle end. The
  scheduling-correctness story: the parallel (hardware) execution of one cycle equals the
  sequential ORAAT execution — proved once, generically, over the log algebra.
- This gives `TSys` directly: `S` = register/memory valuation, `step` = one committed cycle.

## Action language

Intrinsically typed terms (deep embedding): `Action Γ τ` with reads, writes, pure ops
(BitVec kit), `if`, `let`, memory read/write ports. Depth of typing is driven by one
requirement: `View q` (a maintained-view register) demands a DBSP derivative proof *in its
constructor*, so construction is proof-carrying — correct-by-construction views.

## Compiler

`Action` → netlist IR (registers, LUT-expressible combinational nodes, memory ports), with
semantics preservation stated as `TSys` equality against the ORAAT semantics. One-rule
designs first (Acc8's core is a single rule); the log/schedule composition after.

## Memory write ports (`wrPorts`, decided 2026-07-03)

The LNP64-µ Mover phase needs up to three same-cycle writes into one memory
(core store, mover data word, mover status word), priority = phase order.
Toolchain support:

- **EDSL**: `Act.memWrite` carries an explicit `port : Nat` field (no default —
  optionality on an inductive field would still change constructor arity, so all
  call sites/pattern matches were fixed up once; single-writer designs use port 0).
  The port index is *compilation metadata only*: `Act.run` is unchanged in meaning —
  writes apply in rule order, last write wins. `MemDecl` is unchanged; the compiler
  derives the port count as 1 + the largest port index used on that memory.
- **µVerilog**: `MemDef` holds `wrPorts : List (WritePort aw dw)` (uniform list
  replacing the scalar `wrEn/wrAddr/wrData`). `Module.cycle` commits ports in list
  order; the printer emits one guarded nonblocking assignment per port inside the
  single `always @(posedge clk)` block, in order — IEEE 1800 gives last-update-wins
  for multiple nonblocking updates to the same variable in one time step, so the
  formal commit order is standard-conformant (corroborated by iverilog + yosys on a
  three-port collision).
- **Correctness** (`Compile.MemWriteWF`, both conditions decidable): (a) every write
  to a memory carries its declared widths; (b) port indices strictly increase along
  the design's syntactic write order (`portTrace` Pairwise `<`) — so each port has at
  most one write per cycle and the ascending commit order linearizes the run order.
  Under this WF, `compile_cycle_mems` (proved, generic, sorry-free) gives the memory
  half of the emission theorem via a write-log factoring: `run_memLog` (the design
  cycle replays its executed write log), `memPort_correct`/`rules_memPort` (each
  compiled port evaluates to the log's last write on that port), and
  `range_commit_applyLog` (ascending port commits replay a port-sorted log).
- The Lnp64u core assigns core-store → port 0, mover data → port 1, mover status →
  port 2, satisfying the WF syntactically.

## D12 — read validity is a decidable design-time check (decided 2026-07-29)

`Expr.eval` is total: reading an undeclared register, or a declared one at
the wrong width, denotes the environment's default entry (zero at reset,
never written, therefore constant zero) rather than being an error. The
printed Verilog for the same read references an identifier with no matching
declaration — an implicitly declared, undriven net, i.e. X. The gap between
"denotes zero" and "is X in the artifact" is semantic, not cosmetic, so
read discipline is load-bearing for any claim connecting the denotation to
the artifact.

The obligation deliberately does **not** live inside `Compile.DesignWF`
(which constrains writes and is the precondition of `compile_cycle`), and
it does **not** become a per-design proof burden. It is the existing
decidable check `Symbolic.designReadsValidB design program` — every
register read in every rule body resolves in the program at its intrinsic
width, every source register is found by name at its declared width, and no
register name collides with the canonical `n<k>` wire namespace — whose
acceptance yields `Symbolic.DesignReadsValid` via
`designReadsValidB_sound`. A concrete design discharges it by kernel
reduction once, exactly like `designWFCheck`; `toProgram_denotes` carries
it as the hypothesis `designReadsValidB d d.toProgram = true`. This is the
same shape as D9 (last-write-wins): a semantic contract pinned by a
decision rather than left implicit in a total evaluator.

Empirical acceptance (measured 2026-07-29): `designReadsValidB` returns
`true` for both shipped designs — Acc8 and LNP64-µ against their
`toProgram` witnesses — consistent with the kernel-checked
`DesignReadsValid` conjunct in each release. Cost caveat: the direct
`#eval` took 187 minutes on LNP64-µ under the interpreter (the check does
a linear `find?` over 825 registers at every read leaf). Before the
hypothesis joins a release path, either give the check a compiled entry
point or profile its kernel-reduction behaviour — the §B rule about
profiling decoders before committing applies to it verbatim.

## D13 — emission well-formedness is a decidable module check (decided 2026-07-29)

Proving the generic wire-graph conjuncts of `toProgram_denotes`
(`toProgram_wireWellFormed`, `toProgram_wireMatches`) exposed obligations
on the *compiler's output expressions* that no existing hypothesis
implies: every register read resolves in the module's declarations at its
intrinsic width under a name outside the `n<k>` wire namespace
(`designReadsValidB` checks this at the design level, but the theorem
needs it on `Compile.compile d`'s trees); every memory read resolves at
both its address and data widths (checked nowhere — `designReadsValidB`
covers registers only); and every `slice`/`sext` site has the positive
widths the release checker's arithmetic guards assume (zero-width slices
would flunk `lo ≤ hi`).

Per the D12 rule — strengthen the decidable check, not the theorem's
proof burden — the obligation is one Boolean, `SSA.moduleEmitOkB
(Compile.compile d)`, whose soundness (`moduleEmitOkB_sound` →
`ModuleEmitOk` → `flattenModule_wf`) feeds the flatten-soundness
invariant `FlattenSt.WF`. Both wire-graph theorems carry it as their
single hypothesis; a concrete design discharges it by kernel reduction
once. Measured: Acc8 evaluates to `true` in under a second. LNP64-µ has
*not* been evaluated interpreted — `exprEmitOkB` walks expression trees
without pointer memoization, so the shared-DAG blowup that forced
`flatten`'s `implemented_by` twin applies verbatim; before this
hypothesis joins a release path for LNP64-µ it needs a memoized twin or
kernel-reduction profiling, exactly like the D12 cost caveat.

## D14 — CSE soundness needs identifier discipline (decided 2026-07-29)

`flatten` (and the printer it mirrors) hash-conses SSA nodes on rendered
strings. Equal keys must imply equal structural nodes, or a CSE hit
could alias two semantically different expressions — and that
implication is FALSE for adversarial names: a register literally named
`"a + b"` renders identically to the addition of registers `a` and `b`.
The semantic half of `toProgram_denotes` therefore carries
`moduleNamesOkB`: every register and memory name is an identifier token
(`[A-Za-z_][A-Za-z0-9_]*`). Under it, `keyOf_injective`
(`Loom/Release/KeyInjective.lean`) recovers the node from its key by
leftmost-separator classification. The discipline is what the printed
Verilog's lexical rules already assume, so it constrains nothing a
synthesizable design could do. Companion check `moduleMatchOkB`:
`sext` strictly widening and `zext` non-narrowing — the release matcher
recognizes only those forms, and `flatten`'s degenerate-sext
normalizations (`.ident`/`.slice`) have no matcher case by design.

With D12–D14, `toProgram_denotes` is a proved theorem (2026-07-29, zero
sorries, closure exactly propext/Classical.choice/Quot.sound)
conditional on exactly four kernel-reducible Booleans: `moduleEmitOkB`,
`moduleMatchOkB`, `moduleNamesOkB` on `Compile.compile d`, and
`designReadsValidB d d.toProgram`. Acc8 passes all four by `#eval` in
seconds; LNP64-µ discharge awaits pointer-memoized twins for the
tree-walking checkers (the D12/D13 cost caveat applies to all four
verbatim).

## D15 — input ports are environment-owned state coordinates (decided 2026-07-30)

Real FPGA bring-up (the `Machines/Substrate` ports; next, the lnp64mini
core) needs open designs: modules with input pins driven by the outside
world. The chosen mechanism adds **no expression constructor and no
evaluation parameter**: `Design.inputs : List InputDecl := []` declares
names that expressions read with the ordinary `Expr.reg`, that no rule may
write (`DesignWF.regWrites` already confines writes to declared
registers), and that the *environment* drives between clock edges. The
open-cycle semantics is one definition: `cycleOpen ι σ = cycle
(σ.setInputs inputs ι)` — poke the input coordinates, then run the
ordinary closed cycle. D9's discipline extends verbatim: every read
observes the pre-cycle state *and the input pins as of the clock edge*.

Consequences, in exchange for one field and four small definitions:

- The compiler maps `inputs` to µVerilog `input wire` ports (`Module.ins`)
  and emits no register for them; the printers change only in the header.
  Since neither `Module.cycle` nor `Design.cycle` writes undeclared
  coordinates, both sides preserve input coordinates identically and the
  emission theorem extends to open designs as a corollary
  (`compile_cycleOpen`), not a re-proof. The whole 2026-07-30 inventory of
  the alternative (an `Expr.input` constructor + evaluation parameter):
  24 exhaustive match sites, 15+ inductive proofs, 40+ theorem files —
  all untouched under this design.
- A theorem about an open design quantifies over input valuations, so it
  is agnostic to *who* drives the pins — external world, testbench, or
  another design. This is the seed of the reusable-module story:
  composition is a future flatten-and-substitute operator (wire B's input
  reads to expressions over A's registers) plus an assume-guarantee
  transport lemma over `runOpen`; nothing in the core needs to change for
  it.
- Name hygiene (inputs disjoint from registers/memories, no duplicates)
  is checked at emission time (`Design.emit` errors out), not carried in
  `DesignWF` — extending that structure would ripple into the generated
  release certificates for designs that cannot have inputs anyway.
- The release/SSA witness path is unaffected: release designs are closed
  (`ins = []` default), and no Expr/Act syntax changed.

## D19 — sync-read memories are a decidable shape discipline (decided 2026-07-30)

Full record: `Loom/Hw/D19_SPEC.md`.

µVerilog memories have synchronous write ports and *asynchronous*
in-expression reads, which on an FPGA means distributed LUTRAM: the
lnp64mini dual core sat at 93–100 % of an XC7Z020's LUT sites with 138/140
block RAMs idle. Block RAM needs a *registered* read.

The EDSL could already express one — a rule writing a register whose whole
value expression is a bare `memRead` compiles to `rdreg <= n_k;` beside
`wire n_k = mem[n_a];`, which is exactly yosys's `memory_dff` merge
pattern. Three isolated yosys probes showed the emitted form already
merges; what was missing was a *check* that a memory is read **only** that
way, since one combinational operator in the path, or two read sites whose
address expressions the printer's hash-consing fuses into one wire, demotes
the whole memory back to LUTRAM silently.

So D19 adds **no `Expr` constructor, no AST field, no printer statement and
no emission path** — it adds `Design.syncReadOkB d m` (`Loom/Hw/SyncRead.lean`),
one kernel-reducible Boolean per memory checking (S1) every `memRead` of `m`
is the entire value of an `Act.write`, (S2) one destination register per
site with exactly one write site each, (S3) pairwise distinct address
expressions (`Expr.key` renders as the printer does, so "distinct keys" is
"distinct printer wires"), (S4) declared widths. This is the D12/D13/D14
pattern: strengthen the decidable check, do not grow the framework.

Because no semantic function reads the flag, the emitted text of a passing
design is byte-identical to what it was before, so `compile_cycle`,
`compile_cycle_mems`, `compile_cycleOpen`, `toProgram_denotes` and the
round-trip theorem hold **verbatim and unrestated** — the strongest form of
"emission theorem unaffected". A `syncReadOkB` on `MemDecl`/`MemDef` as a
*field* was rejected on the D15 rip criterion: `MemDecl` is built by
anonymous constructor inside a theorem statement (`Acc8/Theorems/AEV.lean`)
and `MemDef` is destructured across `RoundTrip`, `MatchesSemantics`,
`Release/SSA`, `Release/ToProgram*`, `ArtifactCert` and `ReleaseCertGen`.

Standing caveat the check does *not* discharge: a block-RAM read port and
the write port are different physical ports, and Xilinx 7-series TDP RAM
leaves read data indeterminate on a same-address same-cycle collision,
where `Design.cycle` says "old data". Machines with independent read/write
addresses must argue their colliding cycles are unobservable.

## Order of construction

1. `Action`/`Rule`/ORAAT semantics + `TSys` instance (task 1.10)
2. Acc8 core as the first user; lockstep vs Acc8 ISS (task 1.11)
3. LNP64-µ multicycle core (task 1.11)
4. Netlist IR + verified compiler (tasks 2.1–2.2)
5. `View` construct + DBSP normalizer when the readiness OR-tree and sweep aggregation
   need them (task 3.3)
