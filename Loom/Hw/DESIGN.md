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

1. `Action`/`Rule`/ORAAT semantics + `TSys` instance (task 1.10)
2. Acc8 core as the first user; lockstep vs Acc8 ISS (task 1.11)
3. LNP64-µ multicycle core (task 1.11)
4. Netlist IR + verified compiler (tasks 2.1–2.2)
5. `View` construct + DBSP normalizer when the readiness OR-tree and sweep aggregation
   need them (task 3.3)
