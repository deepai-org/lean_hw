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
8. **Scaling limit (side A sharing).** `Parse.parse` rebuilds the printer's
   SSA wires as expression *trees*, so a wire referenced *k* times is
   blasted *k* times and the CNF grows with the expanded tree rather than
   the DAG. On `s13soak` this is visible in one register (`err`:
   5 962 614 clauses, 10 990 349 LRAT lines, 148 s of the design's 154 s,
   9.4 GB peak RSS); every other signal is under 200 k clauses. The fix is
   pointer-identity memoization of the blaster (the pattern
   `Print.printImpl` uses), which needs an `unsafe` twin and an audit
   whitelist entry — deliberately not taken in v1.
9. **`lnp64mini_soc` is out of v1 scope for two independent reasons**, both
   reported by the tool: it declares D15 *input ports*, which the
   round-trip parser predates and cannot read, and it declares memory
   arrays. Synthesis itself is unproblematic (below); the blocker is side A,
   not solver scale.

## Results (2026-07-31, yosys 0.33, cadical 1.5.3, one x86-64 core)

Verbatim summary lines from `scripts/eqcheck.sh`:

```
EQCHECK OK (2 signals, 741 clauses, LRAT-verified)          s0blinky   (0.03 s)
EQCHECK OK (4 signals, 367 clauses, LRAT-verified)          satcounter (0.03 s)
EQCHECK OK (6 signals, 331 clauses, LRAT-verified)          pingpong   (0.03 s)
EQCHECK OK (58 signals, 6216966 clauses, LRAT-verified)     s13soak    (154 s)
```

Negative control (`scripts/eqcheck.sh --negative-control satcounter`): one
`LUT6` `INIT` bit flipped in a copy of the netlist ⇒

```
[FAIL] reg sat  w=1 vars=33 clauses=72 lrat=0 2ms
       COUNTEREXAMPLE (a state where the two transition functions differ):
       count[1]=0 count[0]=0 … sat[0]=0 rst[0]=0
EQCHECK FAILED (1 of 4 signals differ)
```

`lnp64mini_soc` scale attempt: `synth_xilinx` completes in 89 s
(25 301 cells: 6 595 LUT6, 6 121 FDRE, 527 CARRY4, 13 RAMB36E1, 24 RAM64M;
26 MB of JSON), and `eqcheck` stops immediately at side A with the two
reasons of deviation 9. Follow-up work, in order: D15 input ports in the
round-trip parser, memory ports per §Scope, then the sharing-preserving
blaster of deviation 8.
