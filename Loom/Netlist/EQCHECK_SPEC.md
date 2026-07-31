# Post-synthesis equivalence checker spec (D22 candidate) — binding decisions

Purpose: convert the yosys-adequacy assumption into a per-build checked
artifact. For each emitted module `rtl/X.v`, run yosys's synthesis to a
LUT/FF-mapped netlist and check, bit by bit, that the netlist's one-cycle
transition function equals the µVerilog `Module`'s — every UNSAT verdict
certified by an LRAT proof checked with the PROVED checker
(`Loom.Dp.Cert.checkLrat`). TCB delta: zero new axioms. The CNF encoder is
untrusted in v1 (claim: "if the encoding is faithful, netlist ≡ module";
encoder verification is future work — state this precisely in the tool
output and the spec).

## Scope and comparison object

- Compare the EMITTED core module only (`rtl/s0blinky.v`, `rtl/s13soak.v`,
  …) — not the board wrapper (primitives/CDC are outside the claim, per
  D15/D21). Netlist produced LOCALLY:
  `yosys -p "read_verilog rtl/X.v; synth_xilinx -flatten -nowidelut; write_json out/X.json"`
  (the build_oxc7.sh recipe minus board steps; yosys 0.33 at /usr/bin).
- v1 targets register-only designs end-to-end: s0blinky, satcounter,
  pingpong, s13soak. Designs with memories (s0bscan, lnp64mini*): check
  all registers + module outputs + each memory write port's en/addr/data
  cones and each read-port address cone; the array storage itself is
  carried by cell identity (RAMB/RAM*M) — documented v1 boundary. If that
  is awkward, ship register-only designs first and record the memory plan.
  **(2026-07-31: memory designs are in. See §Memories below for exactly
  what is and is not covered.)**

## Architecture (new dir Loom/Netlist/, new exe Tools/EqCheck.lean)

1. `Cells.lean` — semantics of the cell library synth_xilinx emits:
   LUT1..LUT6 (truth table from the INIT parameter), FDRE/FDSE/FDCE/FDPE
   (D-FF with CE and sync/async set/reset — treat async S/R as sync for
   the transition-function comparison ONLY if the design never exercises
   them, i.e. require they are tied to constants; else fail loudly),
   CARRY4 (CO/O chain), MUXF7/MUXF8, INV, VCC/GND, and pass-throughs
   (BUFG/IBUF/OBUF treated as wires). Unknown cell type = hard error
   naming it.
2. `Json.lean` — parse yosys `write_json` (use `Lean.Data.Json`): modules
   → cells (type, parameters incl. INIT as bitstring, port directions,
   connections as net ids), netnames (for register/port matching), top
   ports.
3. `Netlist.lean` — build the netlist's combinational cone map: for each
   FF, its D-input cone over {FF Q outputs, module inputs, constants};
   for each output port, its cone. Detect combinational loops = error.
4. `Miter.lean` — shared-input Tseitin CNF of both sides:
   side A = the IR `Module` next-expressions (reuse/mirror the Expr
   structure; widths blasted to bits), side B = netlist cones. One miter
   per matched signal-bit; solve each with incremental variable reuse in
   one CNF per signal (or one per design — implementer's choice; report
   solver wall time).
5. Matching: module input ports by name/width (bit i of `name` ↔ netlist
   bit net `name[i]`); registers by FF output netnames (yosys keeps
   `\reg_name` after flatten; handle the `$`-prefixed duplicates by
   requiring a bijection — any unmatched FF or unmatched IR register is a
   FAILURE with a clear report, not a skip). Module outputs by port name.
6. Solver leg: write DIMACS, run cadical (available on PATH or vendor the
   invocation used by scripts/crosscheck_lrat.sh), get ASCII LRAT, feed
   `Loom.Dp.Solver.parseLrat` → `Loom.Dp.Cert.checkLrat` (the PROVED
   checker). SAT (a real difference) → print the countermodel mapped back
   to signal names.
7. `Tools/EqCheck.lean` + lakefile `lean_exe eqcheck`:
   `lake exe eqcheck rtl/X.v out/X.json` → per-signal PASS/FAIL table +
   summary verdict `EQCHECK OK (N signals, M clauses, LRAT-verified)`.

## Acceptance (run all; put verbatim outputs in the final report)

- s0blinky, satcounter, pingpong, s13soak: `EQCHECK OK`, every UNSAT
  LRAT-verified by the proved checker.
- Negative control: mutate one LUT INIT bit in a copied JSON → the checker
  must FAIL with a countermodel (prove the tool can actually see bugs).
- lnp64mini_soc: attempt; if runtime explodes, report where and stop —
  scale work is a follow-up, not this task.
- `lake build` + `lake exe audit` green throughout.

---

## Implementation notes (v1, as built)

Modules: `Loom/Netlist/{Json,Cells,Netlist,Miter}.lean` + `Tools/EqCheck.lean`
(`lake exe eqcheck <module.v> <netlist.json>`), driver `scripts/eqcheck.sh`.
Netlists are generated into a gitignored scratch directory; no generated
artifact enters git.

Side A comes from reading the *emitted text* back with the round-trip
parser `Loom.Emit.MicroVerilog.Parse` — so what is checked is the file the
board build consumes, not an in-memory `Module`. Side B is the netlist.
Both are encoded over the same free variables: one per register bit, one
per input-port bit, and one for `rst`. Registers are compared as
`rst ? init : next` against the flip-flops' realized next state, so the
reset branch is inside the claim.

## Memories (2026-07-31): what is and is not covered

**The cut.** `Parse.parseCut` reads the emitted text with one
substitution: a wire whose whole right-hand side is a memory read,
`wire [dw-1:0] nk = m[a];`, becomes a free symbol `Expr.reg dw "nk"`. The
netlist side is cut at the *same* place — synthesis keeps the wire name,
so the nets called `nk[i]` are seeded with the same free variables. Both
sides therefore read "whatever the array returned this cycle" from one
shared symbol, and everything around the memory is compared exactly.
Identification of the two cut points is by the printer's wire name; no
structural or pointer matching is involved.

**Covered** (checked, LRAT-certified, on every design with memories):

* every register whose cone does not cross a memory boundary — including
  all the logic that *consumes* memory read data, since the read value is
  a shared free variable;
* every module output port;
* every memory **read port's address cone** — side A is the µVerilog
  address expression, side B is the netlist cone at the address wire;
* every memory **write port's enable, address and data cone**, where
  synthesis kept the printed wire's name.

**Not covered**, and reported per signal as `[SKIP] … EXCLUDED: …` with
the reason, counted in the verdict line (`N excluded`) and summarized by a
`NOT COVERED` line:

1. **The array itself.** No claim is made that the RAMB36E1/RAM32M/RAM64M
   (or fabric flip-flops, or LUT ROM) holds the µVerilog array's contents,
   nor that the write ports are wired to the cells the read ports read.
   That is the "carried by cell identity" boundary of §Scope.
2. **Read registers absorbed into a read port** (D19 sync read). yosys's
   `memory_dff` folds `rdreg <= m[a]` into the block RAM's output
   register, so `rdreg`'s bits come out of a RAMB36E1 and it has no
   flip-flop of its own: its *own* transition function is inside the hard
   block. Its *value* is still a shared free variable, so every consumer
   of `rdreg` is checked normally. On `lnp64mini_soc`: 7 registers
   (`a`, `b`, `rdval`, `sel_t`, `sel_f`, `dmem_rd`, `reg_rd`).
3. **Cones that reach an uncut memory read.** When the read register is
   absorbed, the printed read wire's *name* is gone too, so any other
   signal whose cone reaches that memory output is excluded — reported by
   `evalSig` as a `MEMCUT` exclusion, never silently dropped. On the SoC:
   34 signals (`uart_byte`, `wrdata rf.data`, and the 32 `tstateK`, whose
   cones reach `tsleep`'s fabric storage / the retimed bank-select
   flip-flops of the depth-split `RAM64M` reads).
4. **Memory port cones whose wire name synthesis did not keep.** A write
   enable usually gets merged into the RAM's `WE` logic and its `nK` net
   disappears; there is then no netlist signal to compare the cone
   against. 17 such cones on the SoC (1 on `s0bscan`: `bram.en`). This is
   the one class where more coverage is available in principle — comparing
   against the cell's own `WE`/`ADDR`/`DI` pins — at the cost of modelling
   how `memory_libmap` splits an array across cells by width *and* depth
   (`rx_mem` is 4 banks × 3 `RAM64M`), which v2 does not do.
5. **Flip-flops that match no µVerilog register bit.** In a design with
   memories these are array storage realized in fabric (`tsleep` on the
   SoC: 2 048 FDREs — 32 × 64 bits, two write ports and an async read, so
   `memory_libmap` left it in flops) and registers synthesis retimed into
   a memory read path (5 on the SoC: the bank-select address bits of the
   depth-split `RAM64M` reads). They are *tolerated and tracked*: the
   bijection check is still a hard failure on memory-free designs, and any
   *checked* cone that reaches one becomes a reported `MEMCUT` exclusion.
   The same mechanism covers a flip-flop yosys retimes *through* an array
   (`s0bscan`'s `banner` ROM: 7 FDREs driving the cut read wire `n41`,
   yosys having pushed `con_idx`'s register into the ROM read).
6. **Read-wire bits folded to a constant from the array contents.** yosys
   may prove a read-data bit constant *because of what is in the array*
   (`s0bscan`'s `banner[…][7]`, always 0). Such a bit becomes a unit
   assumption, like a constant-folded register bit — but unlike one it has
   no reset branch to discharge it: it is an assumption *about the array*,
   which is exactly what cell identity carries. Counted and printed
   (`N read bit(s) folded to a constant from the array contents
   (assumed)`).
7. **Write-only memories** need no special case: `tp_arr` and
   `sigmask_arr` have write ports and no reads, so their storage is
   unobservable and yosys deletes it; their write cones are checked like
   any other (both are `trivially equal` here).

Unknown cell types remain a hard error naming the cell, memory hard blocks
included: `Cells.memCellPorts` lists RAM32M/RAM64M/RAM32X1D…/RAMB18E1/
RAMB36E1 and friends, and a memory the table does not name is reported as
an unsupported cell, never skipped.

## Deviations

1. **Netlist recipe.** The spec's line is
   `yosys -p "read_verilog rtl/X.v; synth_xilinx -flatten -nowidelut; write_json out/X.json"`.
   As built it is
   `read_verilog rtl/X.v; hierarchy -check -top X; proc; splitnets;
    synth_xilinx -flatten -nowidelut -top X; select X %n; delete; write_json …`.
   * `proc; splitnets` — **required for sound matching.** When yosys folds a
     register bit to a constant, `wreduce` shrinks the multi-bit register
     wire *and reorders the surviving bits*: on `s13soak` the 32-bit
     `maxout` netname came back as 8 bits in the order `bit0 bit1 bit2 bit4
     bit3 …`, so "bit `i` of `name`" could not be recovered from the
     netname. With `splitnets`, every bit is its own netname `name[i]` —
     exactly the matching rule §5 asks for. Cell counts are identical with
     and without it on all four designs.
   * `select X %n; delete` — drops the ~430 blackbox cell-library modules
     `synth_xilinx` leaves in the design (JSON 9.2 MB → 30 kB). The top
     module's JSON is unaffected. A side effect: yosys then omits
     `port_directions`, so port directions are hard-coded per cell type in
     `Cells.lean` (which is where the "unknown cell type = hard error"
     discipline lives anyway).
2. **Constant-folded register bits** are not a failure. yosys's
   `opt_dff`/`wreduce` replace a register bit that provably holds a
   constant from reset by that constant — a *reachability*-justified
   rewrite, so the two transition functions genuinely differ on unreachable
   states. Such bits become unit assumptions on the shared state variables,
   and the assumption is discharged by the same miters that use it: with
   `rst` free, the `rst = 1` branch forces the module's reset value of the
   bit to equal the constant (a comparison of two constants, independent of
   the assumption — the base case) and the `rst = 0` branch is the
   induction step. The verdict is therefore: *the netlist and the module
   have the same one-cycle transition function on every state reachable
   from reset*. `s13soak` has 24 such bits (`maxout[31:8]`); the other
   three designs have none.
3. **Miter granularity**: one CNF per signal *word* (register or output
   port), whose miter output is the OR of the per-bit XORs — the choice §4
   leaves open. Equivalent to per-bit miters; the countermodel names the
   offending state directly.
4. **Trivially-equal signals.** When the encoder's constant folding makes
   both sides literally the same formula (every `assign o = reg` output
   port), the miter reduces to the empty clause: unsatisfiable by
   construction, with no solver run and no LRAT proof to check. These are
   reported `PASS … trivially equal`, and counted in the clause totals.
5. **Clause normalization** (repeated literals dropped, tautological
   clauses dropped) is required for the LRAT leg: cadical discards
   tautologies while parsing, which desynchronizes LRAT clause ids from the
   `CNF Nat` handed to the checker. Observed as `checkLrat` *rejecting*
   cadical's certificates for two `s13soak` registers until normalization
   was added — and reproduced independently with
   `scripts/loom_check_lrat.sh`'s harness on the same files, so it is a
   property of the encoding, not of the driver.
6. **FF `INIT` is ignored**: the comparison drives `D`/`CE`/`R`/`S`
   explicitly, and the power-up value is modelled by the checked `rst`
   branch. Any other flip-flop parameter (`IS_*_INVERTED`) is a hard error.
7. **The LRAT checker is the proved one** (`Loom.Dp.Cert.checkLrat`,
   i.e. Lean core's verified `LRAT.check`) but is *evaluated as compiled
   code*, exactly as the cross-check harness `scripts/loom_check_lrat.lean`
   does — not by kernel `decide`. No theorem depends on the tool; the TCB
   delta remains zero and no new axioms are introduced.
8. **Scaling limit (side A sharing) — FIXED 2026-07-31.** `Parse.parse`
   rebuilds the printer's SSA wires as a shared DAG, but `blastE` walked it
   as a *tree*, so a wire referenced *k* times was blasted *k* times. On
   `s13soak` this showed up in one register (`err`: 5 962 614 clauses,
   ~11.0 M LRAT lines, ~148 s of the design's ~151 s, 9.4 GB peak RSS).
   `blastE` now has the pointer-identity memoized twin the note predicted
   (`Loom/Netlist/Miter.lean`, `attribute [implemented_by blastEM]`), the
   same shape as `Print.printImpl`/`Expr.readsMem`, with its audit
   whitelist entry and a `TRUST.md` paragraph. Effect on `s13soak`:
   **6 216 966 → 45 611 clauses, 158 s → 1.1 s**, same verdict. It is what
   makes `lnp64mini_soc` (881 k clauses, 18 s) feasible at all.
   (Proof sizes vary a little run to run — cadical is not bit-reproducible
   here — so LRAT totals move by a fraction of a percent; clause counts,
   which the encoder determines, do not.)
9. **`lnp64mini_soc` — IN SCOPE 2026-07-31.** The two blockers named here
   (the round-trip parser predating D15 input ports; memory arrays) are
   both gone: `Parse` reads input ports into `Module.ins` (with the
   round-trip theorem extended and a kernel-checked open-module instance),
   and memories are handled at the boundary described in §Memories. The
   verdict is `EQCHECK OK (362 signals, 58 excluded, …)` — see §Results.
10. **Unmatched flip-flops are a hard failure only without memories.** §5
   asks for a bijection, "any unmatched FF is a FAILURE, not a skip". That
   still holds for memory-free designs. With memories, array storage in
   fabric and registers retimed into a read path make it unachievable
   without modelling the array; the check is downgraded to a printed
   exclusion, with `evalSig` turning any *checked* cone that reaches such a
   flip-flop into a reported `MEMCUT` exclusion. So an unmatched flip-flop
   can still never be silently absorbed into a PASS.
11. **The round trip on emitted files.** `lake exe rtlroundtrip rtl/*.v`
   (new, wired into `scripts/ci.sh`) parses each emitted file and requires
   reprinting it to reproduce the bytes: 12 files pass, including
   `lnp64mini`, `lnp64mini_dual`, `lnp64mini_soc`, `s0bscan` and `acc8`.
   `rtl/lnp64u.v` is skipped *with its reason printed*: at 188 k lines it
   exhausts the default 8 MB stack in the parser's non-tail line recursion
   — a scale limit of the parser, not of what it accepts, and unrelated to
   input ports (`lnp64u` declares none).

## Results (2026-07-31, yosys 0.33, cadical 1.5.3, one x86-64 core)

Verbatim summary lines from `scripts/eqcheck.sh` (v1, before memories and
before the memoized blaster):

```
EQCHECK OK (2 signals, 741 clauses, LRAT-verified)          s0blinky   (0.03 s)
EQCHECK OK (4 signals, 367 clauses, LRAT-verified)          satcounter (0.03 s)
EQCHECK OK (6 signals, 331 clauses, LRAT-verified)          pingpong   (0.03 s)
EQCHECK OK (58 signals, 6216966 clauses, LRAT-verified)     s13soak    (158 s)
```

### v2 (2026-07-31): input ports, memories, memoized blaster

```
EQCHECK OK (2 signals, 0 excluded, 741 clauses, LRAT-verified)        s0blinky      (0.03 s)
EQCHECK OK (4 signals, 0 excluded, 367 clauses, LRAT-verified)        satcounter    (0.03 s)
EQCHECK OK (6 signals, 0 excluded, 331 clauses, LRAT-verified)        pingpong      (0.03 s)
EQCHECK OK (58 signals, 0 excluded, 45611 clauses, LRAT-verified)     s13soak       (1.1 s)
EQCHECK OK (17 signals, 1 excluded, 6172 clauses, LRAT-verified)      s0bscan       (0.2 s)
EQCHECK OK (362 signals, 58 excluded, 881423 clauses, LRAT-verified)  lnp64mini_soc (18 s)
```

`lnp64mini_soc` header, verbatim:

```
  netlist: 25301 cells, 6123 flip-flops, 212 ports
  matched: 191 registers (4612 bits, 94 constant-folded), 191 output ports (4612 bits), 19 inputs
  memories: 8 array(s), 11 read site(s) (2 cut at the printed wire, 9 absorbed
    into a read port), 9 write port(s); 7 read register(s) inside a hard block,
    0 flip-flop(s) retimed inside a cut read, 0 read bit(s) folded to a constant
    from the array contents (assumed)
  2053 flip-flop(s) match no µVerilog register bit — memory array storage
    realized in fabric, or registers retimed into a memory read path …
```

The 58 SoC exclusions, by reason (each printed per signal): 32 cones
reaching memory storage / a retimed flip-flop (`tstate0…31`), 17 memory
port cones whose printed wire name synthesis did not keep, 7 read
registers absorbed into a RAMB36E1, 2 cones reaching an uncut memory data
output (`uart_byte`, `wrdata rf.data`).

The negative control is unchanged (`scripts/eqcheck.sh
--negative-control`): one flipped `LUT6` `INIT` bit ⇒ `EQCHECK FAILED
(1 of 4 checked signals differ)` with a countermodel.

Negative control (`scripts/eqcheck.sh --negative-control satcounter`): one
`LUT6` `INIT` bit flipped in a copy of the netlist ⇒

```
[FAIL] reg sat  w=1 vars=33 clauses=72 lrat=0 2ms
       COUNTEREXAMPLE (a state where the two transition functions differ):
       count[1]=0 count[0]=0 … sat[0]=0 rst[0]=0
EQCHECK FAILED (1 of 4 signals differ)
```

`lnp64mini_soc` synthesis is unchanged: `synth_xilinx` completes in ~90 s
(25 301 cells: 6 595 LUT6, 6 121 FDRE, 527 CARRY4, 13 RAMB36E1, 24 RAM64M,
11 RAM32M; 26 MB of JSON). `eqcheck` then takes ~18 s. The whole
acceptance list — six designs, synthesis included — is ~2 min.

Follow-up work, in order: (1) compare memory *port* cones against the
cells' own `WE`/`ADDR`/`DI` pins, which needs a model of how
`memory_libmap` splits an array by width and depth, and would retire
exclusion class 4 (and, for fabric-resident arrays like `tsleep`, class 5);
(2) verify the CNF encoder itself, which is the standing v1 caveat.
