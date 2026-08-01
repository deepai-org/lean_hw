# Post-synthesis equivalence checker spec (D22 candidate) — binding decisions

Purpose: convert the yosys-adequacy assumption into a per-build checked
artifact. For each emitted module `rtl/X.v`, run yosys's synthesis to a
LUT/FF-mapped netlist and check, bit by bit, that the netlist's one-cycle
transition function equals the µVerilog `Module`'s — every UNSAT verdict
certified by an LRAT proof checked with the PROVED checker
(`Loom.Dp.Cert.checkLrat`). TCB delta: zero new axioms. The CNF encoder was
untrusted in v1 (claim: "if the encoding is faithful, netlist ≡ module");
**D32 (2026-08-01) removed that conditional on side A** — see
§"The encoder, proved (D32)" below for exactly which half of the encoder is
proved and which is not.

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
  **(2026-07-31: memory designs are in. 2026-08-01, D31: the "carried by
  cell identity" boundary is GONE — reset images, write-port pins and both
  read shapes are checked per bank. See §Memories for exactly what is and
  is not covered now.)**

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

## Memories (D31, 2026-08-01): what is and is not covered

Until 2026-08-01 a memory was a *cut point* and nothing else: the array's
contents, the wiring of its ports and its configuration image were "carried
by cell identity", i.e. trusted. D30 is what that cost — yosys mapped the
epoch engine's 512×3 `cell_flags` to distributed LUT RAM, the configuration
path silently dropped its non-zero reset image, no stage warned, and the
defect surfaced as `-BADREF` on silicon. D31 brings memories inside the
miter. `Loom/Netlist/Mem.lean` is the model; `Tools/EqCheck.lean` drives it.

### The cut (unchanged, and still the frame)

`Parse.parseCut` reads the emitted text with one substitution: a wire whose
whole right-hand side is a memory read, `wire [dw-1:0] nk = m[a];`, becomes
a free symbol `Expr.reg dw "nk"`. The netlist side is cut at the *same*
place, so both sides read "whatever the array returned this cycle" from one
shared symbol and everything around the memory is compared exactly. What
D31 adds is a second, *structural* comparison of the array itself, so that
the shared symbol is no longer the end of the story.

### Banks

Each netlist memory primitive is resolved into a width/depth-explicit
interface (`Mem.CellIface`): its write address / enable / clock / data pins,
its read ports, whether its reads are synchronous, and the configuration
image its `INIT*` parameters encode — for `RAM32M`/`RAM64M` in either of the
two shapes yosys uses (three *data lanes* `DIA/DIB/DIC` over one shared read
address, or *replicated* content with one read port per port letter,
discriminated by whether the `DI` pins are the same nets), and for
`RAMB18E1`/`RAMB36E1` in `SDP` and in `TDP`, where the configured word is
`w/9` groups of nine (eight data bits, one parity bit) split across
`DIADI`/`DIBDI` and `DIPADIP`/`DIPBDIP`.

The primitives named for one µVerilog `MemDef` are then assembled into a
**bank**: an `nRepl × nDepth × nLane` grid covering the declared address ×
data space, with the arrangement taken from yosys's `<mem>.<group>.<index>`
naming. That naming is only a *hint*: every position it predicts is then
checked by a miter, so a wrong hint is a loud failure, never a silent pass.
A memory primitive that belongs to no declared µVerilog memory is a matching
failure; a primitive *shape* the model does not cover is an error naming the
cell.

### 1. Reset images (`meminit`)

Two different claims, both checked per bank:

* **fidelity** — the primitives' `INIT_xx`/`INITP_xx`/`INIT_A..D` parameters
  are decoded to a per-address, per-bit image and compared against
  `MemDef.init` over the whole declared address space. A mismatch names the
  word and the bit. (`x`, an uninitialized location, reads as the `0` the
  fabric delivers.)
* **deliverability** — a bank whose image is non-zero and whose primitives
  are distributed RAM is a **failure even when the netlist's `INIT` is
  faithful**, because the configuration path does not carry a distributed-RAM
  image to the fabric. This is D30, and it is the one that fires on the
  pre-fix epoch netlist under yosys 0.33: 0.33 writes the `RAM64M` image
  faithfully into the JSON *and the bank still comes up all-zero on the
  board*. (yosys 0.38, the openXC7 version, writes `INIT_A..D = 0` outright,
  so there the fidelity check fires too.) The verdict names the bank, the
  primitive type and an instance.

An array with **no** memory primitive is classified rather than assumed:
write-only arrays (`tp_arr`, `sigmask_arr`) are deleted by synthesis because
their storage is unobservable; a written array `memory_libmap` left in fabric
flip-flops (`tsleep`), and a never-written one realized as LUT ROM
(`s0bscan`'s `banner`), keep their image inside the bitstream — flip-flop
`INIT` and LUT truth tables are both delivered. All three are printed
exclusions with that reason: they are not D30 hazards, and the checker says
why rather than staying quiet.

### 2. Storage and write ports (`wrclk`, `wren`, `wraddr`, `wrdata`)

Per bank, per write port, per replica and per depth group:

* the write **clock** pin must be the clock net;
* the write **enable** pins must all be one net, and its cone is mitered
  against `en ∧ ¬rst ∧ (addr[hi:] = g)` — the printed write line lives in the
  `else` arm of `if (rst)`, so no write commits during reset, and a
  depth-split bank must enable exactly its own group. `g` comes from the
  arrangement hint and is *proved* here; a mis-assigned group is a failure;
* the write **address** pins are mitered against `addr[0:k]`, the low bits;
* the write **data** pins are mitered lane by lane against
  `data[l*cellWidth …]`, through the primitive's own word map — which is
  where a mis-wired parity lane shows up (see Deviation 13).

Address and data are compared **under the enable** (`coneMiterUnder`):
`WritePort.commit` consults them only when the port is enabled, and yosys is
entitled to — and does — simplify a memory's `ADDR`/`DI` logic using the
write enable as a don't-care condition.

The one write-port shape not covered is **several µVerilog write ports
sharing one bank**: `Module.cycle`'s per-port fold is last-write-wins in list
order, and the checker models one committing port per primitive rather than
that fold. It is a printed exclusion naming the memory; no shipped design
with a mapped bank has two ports (`tsleep`, which does, is fabric-resident).

### 3. Read paths (`rdaddr`, `rdshape`)

Each netlist read port is matched to a printed read site by *proving* the
address cones equal — the site is discovered, not assumed — and the match is
reported by name. A read port matching no site, or a site matching no port,
is reported.

The read *shape* is then checked against what the design declares (D19,
`Loom/Hw/SyncRead.lean`):

* an **asynchronous** read (LUT RAM, combinational output) is what µVerilog
  means literally; it passes when the primitive's data pins *are* the printed
  read wire's nets, or drive a read register directly;
* a **synchronous** read (block RAM, one cycle) is sound only if the module's
  read feeds a register that `memory_dff` absorbed into the read port — so
  the check is that the primitive's data pins are exactly that register's
  nets. A synchronous primitive whose output is a *combinational* printed
  wire is a failure: the netlist would be a cycle behind the module;
* `DOx_REG` set (a second output pipeline register, two cycles) is a failure,
  and so is a `WRITE_MODE` other than `READ_FIRST` — the µVerilog read
  evaluates against the pre-cycle contents (`syncReadSite_run`).

Matching the data pins to a named µVerilog value is also what ties the read
ports to the cells the write ports write, which the pre-D31 spec explicitly
disclaimed.

### Still excluded, and why

Reported per signal as `[SKIP] … EXCLUDED: …`, counted in the verdict line
and summarized by a `NOT COVERED` line. There is no aggregate class left
that hides a design's own logic:

1. **Depth-split read data.** When a bank is split `n` ways in depth, the
   read value is muxed across groups by logic *outside* the array, so the
   primitives' data pins are not the module's read value. The address cone
   and every write cone are still checked. (`lnp64mini_soc`: `rx_mem`,
   `uart_mem`, 4 groups each; `epochengine`: `cell_flags`, 8 groups.)
2. **Arrays with no memory primitive.** Fabric flip-flops, LUT ROM, or
   deleted write-only storage — see §1. Their transition function is inside
   the cut read wire (ROM) or inside unmatched flip-flops (fabric).
3. **Printed port cones of such arrays**, where synthesis did not keep the
   wire's name; there is no bank to compare against instead.
4. **Read registers absorbed into a read port.** `rdreg`'s own next-state
   function is inside the hard block. Its *value* is a shared free variable,
   so every consumer is checked normally, and D31 now checks that the block
   it comes out of is the bank the module writes.
5. **Cones that reach an uncut memory read.** When a read register is
   absorbed, the printed read wire's name is gone, so any *other* signal
   whose cone reaches that output is excluded — reported by `evalSig` as
   `MEMCUT`, never silently dropped.
6. **Flip-flops that match no µVerilog register bit** (array storage in
   fabric, registers retimed into a read path). Tolerated and tracked: the
   bijection is still a hard failure on memory-free designs, and any
   *checked* cone reaching one becomes a reported `MEMCUT` exclusion.
7. **Read-wire bits folded to a constant from the array contents.** A unit
   assumption about the array with no reset branch to discharge it. Counted
   and printed.
8. **Several write ports on one mapped bank** — see §2.

Unknown cell types remain a hard error naming the cell, memory primitives
included.

### `check_mem_init.py` is now redundant — and kept anyway

`scripts/check_mem_init.py` was the outside-the-path guard that closed D30.
Its rule (a non-zero image must be block RAM with a non-zero `INIT`; an
all-zero image must be matched by all-zero `INIT`s) is now a *strict subset*
of the `meminit` check above, which additionally compares the image word by
word and is inside the certified artifact rather than beside it.

It is **kept deliberately, not deleted**, as an independent second
implementation: a Python reader and a Lean reader of the same netlist
disagreeing is itself a signal, and the two share no code. `scripts/ci.sh`
runs it with its arguments (it was previously invoked with none, which made
it exit 2 — fixed here). `scripts/epoch_ladder.sh` keeps using it as before.
Its `--allow` mechanism has a counterpart in `eqcheck --ack`, with the same
discipline: an acknowledged defect prints in full and is counted; the flag
stops it failing a gate, not being seen.

## The encoder, proved (D32, 2026-08-01)

The v1 verdict read "*if* the encoding is faithful, netlist ≡ module". That
conditional is now discharged for the µVerilog side of the miter, and the
partition is stated by the tool on every run rather than left to this file.

**The theorem** (`Loom/Netlist/MiterProof.lean`):

```lean
theorem encode_sound {w : Nat} (assumps : List Bit) (syms : List (String × Nat))
    (e : Expr w) (hfrag : encVerified e = true)
    (actB : M (Array Bit)) (valB : (Var → Bool) → BitVec w) (hB : EncA 0 w actB valB)
    (hwfA : ∀ b ∈ assumps, BitWF 0 b) {s : St}
    (hrun : M.run (sigMiter assumps syms e actB) {} = (.ok (), s)) :
    CNF.Unsat (toDimacs s.clauses).cnf ↔
      ∀ f : Var → Bool, (∀ b ∈ assumps, b.denote f = true) → e.eval (stOf f) = valB f
```

`sigMiter` is the shape every miter has: the folding assumptions, side A,
side B, and the assertion that the two differ. Both `coneMiter` (output
ports, memory port cones, read-address cones) and `regMiter` are *instances*
of it — `regMiter`'s side A is now written as the µVerilog expression
`mux (reg 1 "rst") (lit init) next` and blasted by the one blaster, which
emits exactly the clauses the old hand-built reset mux did (`reg` and `lit`
blast to nothing), so register miters are inside the theorem too. What is
outside it: the `assertEqs` prefix the tool adds when the matching has
merged register bits (D31's `Matching.eqs`, non-empty only on
`epochengine`), which allocates gate variables of its own before the miter
starts. Both directions are proved:
left to right makes an UNSAT verdict *mean* the two transition functions
agree; right to left makes a SAT verdict *mean* they differ, i.e. it is what
makes the printed countermodel a real disagreement. `stOf f` is the µVerilog
state an assignment describes, and every state is of that form
(`stOf_surj`), so "∀ f" is "∀ state".

**Verified / unverified, the honest partition.**

* **Side A — proved.** `blastE` (`Loom/Netlist/Miter.lean`) is proved to
  encode exactly `Expr.eval`, in both directions, for
  `lit reg and or xor not add sub eq ult mux slice zext sext`
  (`Enc_blastE`). The gate layer under it (`mkAnd`/`mkOr`/`mkXor`/`mkIte`
  and the two list reductions) is proved once in `Loom/Netlist/Encode.lean`:
  each gate's clauses *force* its output (the direction that makes UNSAT
  meaningful) and every partial model extends to satisfy them (the direction
  that makes SAT meaningful).
* **Side A — NOT proved: `shl`, `shr`, `slt`.** The barrel shifter's
  variable-shift structure and the signed comparator resisted proof in the
  time available; they are left on the existing unverified path rather than
  weakening the theorem to admit them. `encVerified` is the decidable
  predicate that selects the proved fragment, and `unverifiedOps` is the
  same information as a list of names; `encVerified_iff` proves the two
  agree, so the tool's report and the theorem's hypothesis are the same
  predicate. `eqcheck` evaluates it over every side-A expression it blasts
  and prints which operators a design uses.
* **Side B — NOT proved.** The netlist cone walk (`Netlist.evalSig` /
  `evalBits`: a fuelled, memoised traversal of the driver map) enters
  `encode_sound` as the hypothesis `EncA 0 w actB valB` — "side B's encoder
  is faithful to *some* semantics". Proving that hypothesis (which needs a
  reference semantics for the netlist and a memo-table invariant) is the
  remaining half of D32. The cell library (`Cells.lean`: LUT `INIT` tables,
  CARRY4, MUXF7/8, the FDRE family) is inside that unproved half.
* **The clause normalization is inside, not beside.** See Deviation 5.

**Cost.** Zero: the proofs are not executed. The encoder's *definitions*
changed shape — `addBits`/`eqBits`/`assertDiffer` became structural
recursions and the elementwise cases use `buildM` — but emit the same
clauses in the same order, and the clause counts are unchanged
(`s0blinky` 741, `satcounter` 367, `pingpong` 331, `s13soak` 45 611). The
memoised compiled twin `blastEM` (`@[implemented_by]`, its audit-whitelist
entry and its `TRUST.md` paragraph) is untouched and still carries the
tool's speed; the reference `blastE` it stands in for is now the *proved*
one, which strengthens that whitelist entry rather than adding to it.

**Verdict lines, verbatim** (`satcounter`, a design entirely inside the
fragment):

```
  encoder side A (the µVerilog expression, Loom.Netlist.blastE): PROVED faithful — Loom.Netlist.encode_sound: the CNF handed to cadical is UNSAT iff the two sides agree on every valuation (clause normalization inside the theorem). Proved operators: lit reg and or xor not add sub eq ult mux slice zext sext. NOT proved: shl shr slt.
  encoder side A: every expression in this design is inside the proved fragment.
  encoder side B (the netlist cone walk, Loom.Netlist.evalSig): NOT proved — it enters encode_sound as the hypothesis `EncA 0 w actB valB`. Every UNSAT is LRAT-certified and re-checked by Loom.Dp.Cert.checkLrat, the proved checker.
EQCHECK OK (4 signals, 0 excluded, 0 acknowledged, 367 clauses, LRAT-verified; encoder side A proved, side B unproved)
```

and on a design that leaves the fragment (`s13soak`, which shifts):

```
  encoder side A: this design uses shl — OUTSIDE the proved fragment, so for the signals whose cones contain them the old conditional claim ("if the encoding is faithful") still applies.
EQCHECK OK (58 signals, 0 excluded, 0 acknowledged, 45611 clauses, LRAT-verified; encoder side A proved except shl, side B unproved)
```

`lnp64mini_soc` reports `shl, slt, shr`; `s0blinky`, `satcounter`,
`pingpong` and `s0bscan` are entirely inside the fragment.

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
   **(D32, 2026-08-01: this normalization is now INSIDE the theorem.)**
   `Loom.Netlist.toDimacs_unsat_iff` proves that normalizing *and* numbering
   the clauses preserves satisfiability in both directions — dropping a
   tautology is sound because the clause is true under every assignment, and
   dropping a repeated literal changes nothing — so `encode_sound` is stated
   about the DIMACS the solver actually reads, not about the pre-normalized
   clause array beside it.
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
   (Superseded by D31: with memories inside the miter the SoC's verdict is
   `441 signals checked, 61 excluded, 2 acknowledged`.)
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
12. **Merged register bits are an equality assumption, not a failure.**
   yosys's `opt_merge` proves two µVerilog register bits' next-state cones
   identical and keeps ONE flip-flop, so two IR bits claim one net. That was
   a hard matching failure (it is what blocked `epochengine`:
   `b_target[0]` and `inval_epoch[0]`). It is now an assumption of the same
   shape as a constant-folded bit — the two transition functions differ only
   on unreachable states — and discharged the same way: with `rst` free, each
   register's own miter compares the two *reset* values in its `rst = 1`
   branch (constants, independent of the assumption: the base case) and its
   `rst = 0` branch is the induction step. `Matching.eqs` carries the pairs;
   `assertEqs` asserts them; `Miter.lean` is unchanged.
13. **A yosys 0.33 defect the write-data check found (`lnp64mini_soc`,
   `dmem`).** In `RAMB36E1` `SDP` at width 72 the netlist wires `DIPBDIP` to
   `DIPADIP`'s nets, so write-data bits 44/53/62 reach no pin while
   `DOPBDOP` *reads* those word positions. The netlist is self-inconsistent
   — whatever layout convention one assumes, the bits written and the bits
   read must be the same — so `dmem` bits 44/53/62 would hold their `INIT`
   forever. It is a synthesizer defect, not an emission one; the ZC702
   bitstream is built with yosys 0.38 through openXC7 and the design runs, so
   0.38 does not have it. Carried as an `--ack` in `scripts/eqcheck.sh` with
   this note, printed in full on every run.
14. **Write address and data are compared under the enable.**
   `WritePort.commit` consults `addr`/`data` only when `en` is set, and yosys
   simplifies a memory's `ADDR`/`DI` logic using the enable as a don't-care
   condition. Comparing them unconditionally reports differences that are not
   differences (it did, on all six `rf` replicas). `coneMiterUnder` asserts
   the guard.

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

### v3 (2026-08-01): memories inside the miter (D31)

`scripts/eqcheck.sh`, verbatim summary lines (yosys 0.33, cadical 1.5.3,
one x86-64 core):

```
EQCHECK OK (2 signals, 0 excluded, 0 acknowledged, 741 clauses, LRAT-verified)
EQCHECK OK (4 signals, 0 excluded, 0 acknowledged, 367 clauses, LRAT-verified)
EQCHECK OK (6 signals, 0 excluded, 0 acknowledged, 331 clauses, LRAT-verified)
EQCHECK OK (58 signals, 0 excluded, 0 acknowledged, 45611 clauses, LRAT-verified)
EQCHECK OK (24 signals, 1 excluded, 0 acknowledged, 7241 clauses, LRAT-verified)
EQCHECK OK (124 signals, 9 excluded, 0 acknowledged, 57987 clauses, LRAT-verified)
EQCHECK OK (441 signals, 61 excluded, 2 acknowledged, 1726821 clauses, LRAT-verified)
```

in order: `s0blinky`, `satcounter`, `pingpong`, `s13soak`, `s0bscan`,
`epochengine` (new: the design D30 was found on), `lnp64mini_soc`. The whole
list, synthesis included, is ~4 min; `lnp64mini_soc` alone is ~90 s of
synthesis and ~55 s of checking.

**The regression fixture.** `Tests/fixtures/eqcheck/epochengine_prefix.{v,
json.gz}` is the epoch engine as it was before `b510caf` — `cell_flags`
still carrying occupancy as a non-zero reset image — with the netlist yosys
0.33 builds from exactly that text. `scripts/eqcheck_memfixture.sh` (wired
into `scripts/ci.sh`, needs only cadical) requires eqcheck to REJECT it, for
the right reason, naming the bank. Verbatim:

```
[FAIL] meminit cell_flags        w=3 vars=0 clauses=0 lrat=0 0ms
       RESET IMAGE NOT DELIVERED for bank 'cell_flags': the image is NON-ZERO
       but synthesis mapped the bank to distributed LUT RAM (RAM64M, e.g.
       'cell_flags.0.0'). The configuration path carries a block-RAM image and
       does NOT carry a distributed-RAM one, so this bank comes up all-zero on
       silicon while simulation says otherwise (D30). 24 × RAM64M (1
       replica(s) × 8 depth group(s) × 3 lane(s)), 512 INIT bit(s) set
EQCHECK FAILED (1 of 124 checked signals differ)
```

Exactly one signal differs — the defect — and the post-fix `epochengine`
passes the same 124 signals. D30 is now reproducible from the certified path
with no board and no simulation.

**The 61 `lnp64mini_soc` exclusions**, each printed per signal, in six
classes with nothing aggregated:

| n | signals | why |
|---|---------|-----|
| 7 | `a`, `b`, `rdval`, `sel_t`, `sel_f`, `dmem_rd`, `reg_rd` | read registers `memory_dff` absorbed into a `RAMB36E1` read port: the next-state function is inside the hard block. D31 now *does* check that the block is the bank the module writes. |
| 32 | `tstate0…31` | cones reaching FDREs that match no µVerilog register bit (`tsleep`'s fabric storage / retimed bank-select flops) — `MEMCUT`. |
| 6 | `rf[r0g0].0 … rf[r5g0].0` | the rf write-data lane-0 cone reaches `rx_mem`'s uncut `RAM64M` output — `MEMCUT`. |
| 1 | `uart_byte` | same, on `uart_mem`'s output. |
| 2 | `uart_mem[r0p0]`, `rx_mem[r0p0]` | depth-split read data (4 groups): the read value is muxed outside the array. Their address cones and every write cone are checked. |
| 13 | `tsleep` + its 6 port cones, `tp_arr`/`sigmask_arr` + their 4 port cones | arrays with no memory primitive: `tsleep` left in fabric flip-flops, the other two write-only and deleted. Their printed port wire names did not survive, so there is nothing to compare a cone against. |

`s0bscan`'s single exclusion is `banner` — a never-written array yosys
realized as LUT ROM, so its contents live inside the cut read wire.
`epochengine`'s nine are three absorbed `RAMB18E1` read registers, three
cones reaching `cell_flags`' uncut `RAM64M` outputs, and `cell_flags`' three
depth-split read ports.

**One acknowledged failure on `lnp64mini_soc`** (`--ack dmem`, printed in
full as an `[ACK]` line): the yosys 0.33 `RAMB36E1` `SDP` parity mis-wiring
of Deviation 13. It is not suppressed and it is counted in the verdict line.

There were **two** until 2026-08-01: `tpc`, the D30 loss on lnp64mini's
thread-PC tables recorded in `EPOCH_SPEC.md` E13, was found here
independently from the certified path — which was the point — and is now
*fixed* rather than acknowledged (D37: the declared image is all-zero and
the `cmd 13` sweep establishes `TEXT_BASE`). D37 also made the same question
decidable at the design, before synthesis: `Loom.Hw.Design.memInitOkB`
predicts the mapping class from the declared shape and asks
`Loom.Hw.imageDelivered` — *this* module's rule, shared verbatim, so a
design-time prediction and a netlist-time measurement cannot disagree about
what "undeliverable" means. The two remain complementary: the prediction can
be wrong about which family yosys picks, and only the netlist knows.

**What the pin-level checks bought.** The 17 "memory port cones whose wire
name synthesis did not keep" and the 1 on `s0bscan` (`bram.en`) are gone as a
class: those cones are now compared against the primitives' own
`WE`/`ADDR`/`DI` pins, which is exactly the follow-up item (1) the v2 spec
named. What replaced them in the count are the printed cones of the three
arrays that have *no* primitive to compare against.

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

(v2 figures, kept for comparison.) `lnp64mini_soc` synthesis is unchanged:
`synth_xilinx` completes in ~90 s
(25 301 cells: 6 595 LUT6, 6 121 FDRE, 527 CARRY4, 13 RAMB36E1, 24 RAM64M,
11 RAM32M; 26 MB of JSON). `eqcheck` then takes ~18 s. The whole
acceptance list — six designs, synthesis included — is ~2 min.

Follow-up work, in order: ~~(1) compare memory *port* cones against the
cells' own `WE`/`ADDR`/`DI` pins~~ **— done, D31, 2026-08-01**, which needed
a model of how
`memory_libmap` splits an array by width and depth, and retired the old
exclusion class 4 entirely. It did *not* retire class 5: an array
`memory_libmap` leaves in fabric flip-flops (`tsleep`) still has no primitive
to compare against, and that is now a printed exclusion of its own.
~~(2) Verify the CNF encoder itself, which is the standing v1 caveat~~
**— done for side A, D32, 2026-08-01; side B (the netlist cone walk) is the
remaining half.**
(3) Depth-split read data and multi-port write ordering, the two shapes D31
leaves excluded.
