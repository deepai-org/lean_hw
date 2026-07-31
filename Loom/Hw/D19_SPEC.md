# D19 — sync-read memories (block RAM) as a decidable shape discipline

**Decided 2026-07-30.** Companion to D15–D18: the smallest change that makes
Loom-emitted regfiles land in FPGA block RAM instead of distributed LUTRAM.

## The problem, measured

`Machines/Lnp64mini` declares `rf` as a 1024×64 memory with one write port
and six read sites. µVerilog has exactly one kind of memory — synchronous
write ports, *asynchronous* in-expression reads (`mem[addr]`) — so
`yosys synth_xilinx` had no choice but distributed RAM. The dual-core SoC
came out at

```
Info:           SLICE_LUTX: 99072/106400    93%
Info:            SLICE_FFX: 18912/106400    17%
Info:            RAMB36E1:      2/  140      1%
ERROR: Unable to find legal placement for all cells, design is probably
       at utilisation limit.
```

138 of 140 block RAMs idle while the design blows the LUT budget. The
hand-written predecessor (`lnp64mini3.v`) fits because its `rf` reads are
*registered* — the read data lands in a pipeline flop, which is BRAM-shaped.

## What was actually broken (probe results, yosys 0.33, xc7z020)

Loom's EDSL can already express a registered read: a rule that writes a
register whose whole value expression is a bare `memRead`. The compiler
emits it, inside the single `always @(posedge clk)` block, as

```verilog
  wire [63:0] n970 = rf[n969];
  ...
      a <= n978;               // n978 = <guard cone> ? n970 : a
```

which is precisely the `memory_dff` merge pattern. Three isolated probes
(`yosys -p "read_verilog; synth_xilinx -flatten -nowidelut; stat"` on a
1024×64 array with a 512×64 companion) pin down what does and does not
survive that merge:

| shape of the read | result |
|---|---|
| `r <= en ? mem[addr] : r` (sync reset in the `if (rst)` arm), 3 distinct addresses | **6 RAMB36E1**, 4 LUT2 |
| one read `r1 <= en ? (z ? 64'd0 : mem[a1]) : r1`, others clean | **0 RAMB**, 640 LUT6 — one dirty read demotes the *whole* memory |
| two read registers sharing one `wire m1 = rf[aa];` | **0 RAMB**, 336 LUT6 |
| 6 read registers, but two pairs share the same *address net* | 0 RAMB for `rf` (1280 LUT6); with `(* ram_style="block" *)` yosys **errors**: `no valid mapping found` |
| 6 read registers, 6 structurally distinct addresses | **13 RAMB36E1**, 6 LUT2 — no attribute needed |

So three things, and only these three, decide the outcome:

1. no combinational operator may sit between `mem[addr]` and the flop;
2. every read site needs its **own** `mem[...]` expression — the printer
   hash-conses on rendered form and yosys `opt_merge` dedups structurally
   equal `$memrd` cells, and a shared read output has fan-out 2, which
   `memory_dff` refuses;
3. the destination register must have no other data source.

None of that requires a new construct. It requires *checking*.

## The decision

**Option (b) of the design brief, in its lightest form: a decidable
well-formedness check, no new `Expr` constructor, no new AST field, no new
emission path.** `Loom/Hw/SyncRead.lean` adds `Design.syncReadOkB d m`,
true iff, for memory `m`:

* **(S1) sanctioned position** — every `Expr.memRead _ m _` node in
  `d.rules` is the *entire* value expression of an `Act.write`; never in a
  guard, inside a larger expression, in a `memWrite` address/data, or in
  another memory's read address.
* **(S2) one register per site, one site per register** — destination
  register names pairwise distinct, and each destination register has
  exactly one syntactic `write` site in the whole design.
* **(S3) pairwise distinct address expressions** — `Expr.key` renders an
  expression the way `Print.pExpr` does, so "distinct keys" is exactly
  "distinct printer wires", which is exactly condition 2 above.
* **(S4) declared widths** — `m` is declared and every site's destination
  width is `m.dataWidth`.

Rejected alternatives, and why:

* **A `syncRead : Bool` field on `MemDecl`/`MemDef` (option (a)).** It
  reads well but it is not minimal-rip: `MemDecl` is built with anonymous
  constructors in `Machines/Lnp64mini/Core.lean` and inside a *theorem
  statement* in `Machines/Acc8/Theorems/AEV.lean`, and `MemDef` is
  destructured by `RoundTrip.MemDef.Matches`, `MatchesSemantics`,
  `Release/SSA.lean`, `Release/ToProgram*.lean`, `ArtifactCert`, and
  `Tools/ReleaseCertGen.lean`. A field that no semantic function reads is
  not worth rippling through the release-certificate path (D15 made the
  same call about `Expr.input`: 24 match sites, 15 inductive proofs, 40+
  theorem files — all untouched by choosing the non-invasive design).
* **A new rule form / read-register convention with its own printer
  statement.** The probes show the *existing* printed form already merges.
  Adding an `if (EN) rd <= mem[ADDR];` statement to `Print.lean` would
  force `Parse.lean` and the round-trip theorem to grow a case for a form
  that buys nothing measurable.
* **`(* ram_style = "block" *)` on the array declaration.** Not needed —
  with six clean read ports yosys picks BRAM unaided (row 5 of the table),
  and when the shape is *wrong* the attribute turns a silent LUTRAM
  demotion into a hard `no valid mapping found` error. That is arguably a
  feature, but it costs a `MemDef` field, so it stays out until a real
  design needs the forcing.

## Emission argument

`syncReadOkB` is read by **no semantic function**: not `Expr.eval`, not
`Act.run`, not `Design.cycle`, not `Compile.compile`, not `Module.cycle`,
not `Print.print`. It is a predicate *about* a design, not a part of one.

**Consequence (the whole emission argument in one line): the emitted text of
a design that passes the check is byte-identical to the text it had before
anyone thought about block RAM, so `compile_cycle`, `compile_cycle_mems`,
`compile_cycleOpen`, `toProgram_denotes`, the A-EV emission theorem and the
round-trip theorem hold verbatim and were not re-elaborated.** There is no
new proof obligation because there is no new emission path. This is the
strongest possible form of "emission theorem unaffected": not "still true
after re-proof" but "not restated".

What the check certifies is a property of that unchanged text. Under
(S1)–(S4), by inspection of `Compile.nextReg` and `Print.pExprM`:

1. the printer emits exactly `(d.syncReadSites m).length` wires of the form
   `wire [dw-1:0] n_k = m[n_a];`, with pairwise distinct `n_a` (S3), each
   referenced by exactly one register's next expression (S1 + S2);
2. that register's next expression is a mux cone whose only non-`n_k` leaves
   are the register itself — `nextReg` prunes every `ite` neither branch of
   which writes the register, and (S2) says no other branch writes it;
3. no other occurrence of `m[...]` exists in the module (S1).

(1)–(3) is the `memory_dff` pattern: `opt_dff` folds the self-feedback mux
into a `$dffe`, `memory_dff` absorbs the `$dffe` — enable, plus the
synchronous reset the printer emits in the `if (rst)` arm — into the
`$memrd` port, and `memory_libmap` then sees an all-synchronous memory it
can place in block RAM. The probe table is the corroboration that this is
what the tool actually does; the full ladder (EDSL ≡ ISS ≡ iverilog on the
emitted RTL) is the corroboration that the *meaning* did not move.

The one Lean lemma the module carries, `syncReadSite_run`, records the
semantic content of a sanctioned site — the value latched is the
**pre-cycle** memory content at the pre-cycle address:

```lean
theorem syncReadSite_run (σ acc : St) (m r : String) {dw aw : Nat}
    (addr : Expr aw) :
    ((Act.write dw r (Expr.memRead dw m addr)).run σ acc).regs r dw
      = σ.mems m (addr.eval σ).toNat dw
```

This is D9, not new physics, but it is the fact the hardware read port has
to reproduce: **read-first, never write-first**.

## Standing caveat: cross-port collisions

A block RAM read port and the write port are different physical ports.
Xilinx 7-series TDP block RAM leaves the read data *indeterminate* when the
two ports touch the same address in the same cycle, whereas `Design.cycle`
says "old data". A design whose read and write addresses are the same net
(`lnp64mini`'s `dmem`: `dmem_rd <= dmem[dmem_a]` against
`if (dmem_we) dmem[dmem_a] <= dmem_wd`) is safe — yosys uses a single port
in READ_FIRST mode, which is well defined. A design with independent read
and write addresses must argue that a colliding cycle is unobservable.
`syncReadOkB` does **not** check this; it is a memory-model obligation on
the machine, recorded per design. (`lnp64mini` discharges it in
`PORTING_SPEC.md`/`DUAL_SPEC.md`: the FSM never reads `rf` in a cycle it
writes `rf`, except for the free-running `reg_rd` JTAG readback latch, whose
value is only sampled with the core stopped.)

## Applying it: `lnp64mini`

Two shape defects, both fixed in `Machines/Lnp64mini/Core.lean` with no
change to the ISS and no change to any register's cycle-by-cycle value.

**(i) The shared read-address mux.** `r1a = (st == S_RD2) ? rs3f : rs1f`
gave `a` (latched in `S_RD`) and `sel_t` (latched in `S_RD2`) *one* address
net, hence one `$memrd`, hence fan-out 2 and no merge. But the latch enables
already key on `st`, so the state mux is redundant: in `S_RD`, `r1a` is
`rs1f` by definition, and in `S_RD2` it is `rs3f`. Reading
`rf[{cur,rs1f}]` at the `S_RD` site and `rf[{cur,rs3f}]` at the `S_RD2` site
computes the same function of the same pre-cycle state — the mux is deleted,
not moved. `r1a`/`r2a` become dead and are removed.

**(ii) The `x0` zero-mux.** `a <= (rs1f == 0) ? 0 : rf[{cur,rs1f}]` puts an
operator between the array and the flop, which (probe row 2) demotes the
whole memory. It is removable because it is *redundant*:

> **Invariant Z.** For every thread slot `t < 32`, `rf[{t, 0}] = 0`.

*Proof (induction on cycles).* `MemDecl.init` for `rf` is `fun _ => 0`, so
Z holds in `Design.reset`. `rf` has exactly one write port, the
`rf_funnel` rule, whose address/data come from the 20 triples of
`rfTriples`. Enumerating them (`Core.lean` lines 584–643): triple 1 (the
zeroing sweep) writes address `zext zctr` — which does cover `{t,0}` — with
data `L64 0`, preserving Z. Every one of the other 19 triples writes an
address `cat55 _ k` whose low five bits `k` are either a nonzero literal
(`L5 2` for the CLONE child's `r2`, `L5 31` for the child's `sp`) or a
register field guarded by an explicit `¬(field = 0)` conjunct in the same
triple's guard (`rdf`, `ld_rd_q`, `clone_dst`, `reg_wsel` — the JTAG
`SET_REG` path included). So no write ever puts a nonzero value at
`{t,0}`. ∎

Under Z, `(rs1f == 0) ? 0 : rf[{cur,rs1f}] = rf[{cur,rs1f}]` pointwise, so
deleting the mux leaves every register — including the read registers `a`,
`b`, `rdval`, `sel_t`, `sel_f` themselves — bit-identical. That is why the
ISS needs **no** change and why the ladder is expected to be, and is,
bit-exact rather than merely equivalent. Note that `reg_rd` never had a
zero-mux: the JTAG readback path already relied on Z.

Z is a machine-level invariant argued by enumeration, not a Lean theorem;
its empirical backstop is the ladder, which compares every architectural
register of the EDSL against the ISS cycle by cycle, and the iverilog
system testbenches, which read `dut.c0_rf[i]` directly.

After the fix `rf` has six read sites with six structurally distinct
addresses — `{cur,rs1f}`, `{cur,rs2f}`, `{cur,rdf}`, `{cur,rs3f}`,
`{cur,rs4f}`, `{cur,reg_sel}` — and `dmem`, `uart_mem` were already clean.
`rx_mem` is *not*: it is read combinationally inside the rf write data
(`S_EX` UART_RX load), so `syncReadOkB "rx_mem"` is `false` and it stays
LUTRAM — 256×8, which is the right answer anyway.

`Machines/Lnp64mini/Emit.lean` discharges the obligation the D12/D13/D14
way: every emit path evaluates `syncReadOkB` on `rf`, `dmem` and
`uart_mem` and refuses to write the file if any is `false`.

## Results (openXC7, xc7z020clg484-1, `synth_xilinx -flatten -nowidelut`)

Full record in `Machines/Lnp64mini/DUAL_SPEC.md` ("Synthesis datapoint").

| | before | after |
|---|---|---|
| soc `SLICE_LUTX` | 44567 (41%) | **37606 (35%)** |
| soc `RAMB36E1` | 1/140 | **13/140** |
| soc `sysclk` post-route | 31.69 MHz | **32.53 MHz** |
| dual `SLICE_LUTX` | 99072 (93%) | **83926 (78%)** |
| dual `RAMB36E1` | 2/140 | **26/140** |
| dual placement | ERROR | **still ERROR** |

yosys `stat` on the bare `lnp64mini_soc` module: `RAM64M` 1432 -> 24,
`RAMB36E1` 1 -> 13. The mechanism works exactly as designed.

**Honest limit.** D19 recovers ~15 % of the XC7Z020's LUT sites and the
single core routes ~3 % faster, but `nextpnr-xilinx` still cannot legalize
the dual's placement at 78 % (reproduced with two placer seeds on the
cached synthesis JSON). D19 was *necessary* for the dual and is *not
sufficient*; the remaining consumer is the per-core 32-entry thread table
(`tpc`/`tstate`/`tsleep`/`tfutex`/`tp_arr`/`sigmask_arr` dynamic
read/write trees), several of whose arrays are themselves D19 candidates
if their reads are restaged through latch registers.
