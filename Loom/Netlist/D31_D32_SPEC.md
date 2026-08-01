# D31 (memories in eqcheck) + D32 (verified encoder) — binding decisions

Two gaps in the post-synthesis equivalence checker, both named in
`LOOM_GAPS.md` and both now in scope. Read `EQCHECK_SPEC.md` first (the
as-built design, §Memories, §Deviations 1–11).

## Why these two, and why now

D30 proved the checker's excluded region is exactly where the tool lies:
yosys silently discarded a memory's reset image on a LUTRAM-mapped bank, and
eqcheck could not see it because array storage is currently "carried by cell
identity" — i.e. trusted. The separate guard `scripts/check_mem_init.py`
catches that one class from *outside* the certified path. Folding it in makes
one artifact instead of a certificate plus untrusted glue.

D32 removes the checker's own conditional. Today the verdict reads "if the
encoding is faithful, netlist ≡ module". The encoder is a small pure function;
proving it removes the last "if" from the strongest link in the chain.

## D31 — memories inside the miter

Cover, per memory:
1. **Storage semantics.** Model the netlist's memory cells (`RAMB18E1`,
   `RAMB36E1`, `RAM64M`, `RAM32M`, and whatever else `synth_xilinx` emits for
   the shipped designs — unknown cell = hard error, as today) as a transition
   over an address-indexed state, and compare against the IR `MemDef`'s
   write-port commit semantics (`Module.cycle`'s per-port fold, ascending
   order, last-write-wins).
2. **Reset images.** The `INIT_xx` parameters (and their absence) must be
   compared against the `MemDecl.init` function the emitted RTL declares.
   THIS is the D30 case: a bank whose netlist init is all-zero while the
   module's image is not must FAIL, loudly, naming the bank.
3. **Read paths.** Async reads (LUTRAM) and D19 sync reads (BRAM, one cycle
   of latency, registered output) are different transition shapes — model both
   and check the design actually got the one it declares (`syncReadOkB`).

Acceptance (all three required):
* eqcheck **fails on the pre-fix epoch netlist**, reproducing D30 from the
  certified path with no board and no simulation. Keep a copy of that netlist
  as a regression fixture.
* eqcheck passes on the current designs, and the SoC's 58 memory-boundary
  exclusions shrink to a *named, individually justified* minimum. Whatever
  remains excluded must be listed with the reason it cannot be checked, not
  aggregated.
* `check_mem_init.py` becomes redundant. Keep it as an independent cross-check
  (two implementations disagreeing is a signal) but say so explicitly in the
  spec; do not delete it silently.

## D32 — the encoder, proved

Statement to prove (adjust names to the code, keep the content):

    encode_sound : ∀ (m : Miter), (cnfOf m).Unsat ↔ ∀ σ, agree m σ

i.e. the CNF handed to cadical is unsatisfiable exactly when the two
transition functions agree on every valuation. Both directions matter: the
forward one is what makes a proof meaningful, the backward one is what makes a
countermodel meaningful.

Practical notes:
* Bit-blasting of `add`/`sub`/`eq`/`ult`/`slt`/`shl`/`shr`/`mux`/`slice`/
  `zext`/`sext` is where the work is. If any operator's encoding resists proof
  in reasonable time, **do not weaken the theorem** — leave that operator
  routed through the existing unverified path, have the tool SAY which
  operators are verified and which are not in its verdict line, and record it.
  A partially-verified encoder that is honest about the partition is worth far
  more than a fully-verified one that shipped by weakening its statement.
* Deviation 3 in EQCHECK_SPEC (clause normalization dropping repeated literals
  and tautologies, required because cadical discards tautologies at parse time
  and desynchronises LRAT ids) is part of the encoder and must be inside the
  theorem, not beside it.
* The proof must not slow the tool: keep the fast path `@[implemented_by]`
  as the repo already does, with the audit whitelist entry and rationale.

## Docs to update when these land (part of the goal, not optional)

* `EQCHECK_SPEC.md` — §Memories rewritten to what is now covered; §Deviations
  updated; the verdict line's exact wording recorded.
* `README.md` — the paragraph added 2026-08-01 says the CNF encoder is
  untrusted in v1 and memory-boundary signals are excluded. Both claims change;
  the README must state precisely what is then true, no more.
* `TRUST.md` / `TCB.md` — if the trusted list shrinks, say so there; if it does
  not (e.g. partial encoder verification), say that instead.
* `LOOM_GAPS.md` — move D31/D32 to the closed table with what discovered each.
* `fpga/zc702/README.md` — the epoch entry cites the D30 story; add that it is
  now caught by the certified path.
