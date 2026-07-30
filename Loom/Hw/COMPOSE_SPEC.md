# Compose layer spec (D16 candidate) — binding decisions

Goal: reusable modules per D15's promise. Three pure functions over
`Design` (ordinary data — no core semantics changes), plus the signal
traversal they need. Everything additive; existing proofs untouched.

## New Expr/Act traversals (Loom/Hw/Syntax.lean or new Rename.lean)

- `Expr.mapSignals (f : String → String) : Expr w → Expr w` — rename every
  `.reg` name and `.memRead` mem name. Pure structural recursion (new
  function; adding it breaks nothing).
- `Expr.substReg (n : String) (w : Nat) (e : Expr w) : Expr w' → Expr w'`
  — replace reads `.reg w n` by `e` (width must match exactly; a read of
  `n` at a different width is left untouched — WF rules it out).
- `Act.mapSignals f` / `Act.substReg n w e` — same over write targets
  (mapSignals renames write/memWrite targets too; substReg does NOT touch
  write targets — inputs are never written).

## The three combinators (new file Loom/Hw/Compose.lean)

- `Design.prefixed (p : String) (d : Design) : Design` — rename every
  reg/mem/input name `n` to `p ++ n` (rules' bodies via mapSignals,
  decls, rule names). Instantiation = prefixing.
- `Design.par (a b : Design) : Design` — concatenate regs/mems/rules/
  inputs (caller guarantees disjoint names via prefixed; a decidable
  `parOkB` check is provided for `Design.emit`-style runtime guards).
  Rule order: a's rules then b's (disjoint names ⇒ order between the two
  groups is semantically irrelevant; document, don't prove yet).
- `Design.connect (d : Design) (wire : (n : String) → (w : Nat) →
  Option (Expr w)) : Design` — for each input i with `wire i.name i.width
  = some e`: drop i from inputs and substitute e for reads of i in every
  rule body. e is over the composed design's signals (typically another
  instance's registers — combinational same-cycle wiring, exactly a
  Verilog port connection to a reg output).

`compose` idiom (document in the file header):
```
((a.prefixed "u0_").par (b.prefixed "u1_")).connect
  (fun n w => if n = "u1_cmd_in" then some (.reg w "u0_out") else none)
```

## Theorems: NONE required now (goal defers them). Design for provability:
keep each combinator a small total function; note in docstrings the
intended lemmas (prefixed = bisimulation; par = product; connect
instantiates the input trace of the open simulation).

## The all-Lean bitstream (Machines/Lnp64mini/Soc.lean)

Port to Loom designs (spec source in remote-fpga fpga/substrate0/rtl/):
1. `axi_hp_master.v` (~120 lines): FSM over the simple handshake
   (start_rd/start_wr/addr/wdata → AXI3 single-beat + done/rdata/busy).
   Inputs: AXI slave-side responses (awready/wready/bvalid/bresp/arready/
   rvalid/rdata/rlast...); outputs: the AXI master signals (registers).
2. `axi_gp_master.v` (~110 lines): same shape, 32-bit.
3. The BSCAN register surface currently in lnp64mini_top.v's UPDATE-domain
   case (read mux + rd_reg) CANNOT move into Loom (DRCK/UPDATE clock
   domains). What CAN: nothing further — the DR shift/CDC stays wrapper by
   D15 design. Scope the claim precisely: "all single-clock sysclk logic
   is Lean-emitted"; the wrapper keeps only clock buffers, POR counters,
   BSCANE2+DR+CDC (3 always blocks), PS7.
4. `Soc.lean`: soc = (lnp64mini core).par(hp master "hp_").par(gp master
   "gp_") .connect (core m_done/m_rdata/m_busy ← hp master outputs;
   hp start/addr/wdata ← THE HP MUX — needs core-owns logic as an Expr
   over core st/running and the jtag regs: build the mux expression here
   in the connect wiring, absorbing the wrapper's hp_core_owns into
   Lean); same for gp. Remaining soc inputs = AXI slave responses + cmd_*
   (wrapper); outputs = AXI master signals + observability.
5. Validation ladder: ISS for the masters mirrored in Lean; iverilog tb
   drives the soc's AXI ports with a behavioral AXI slave; loomcheck.s
   again; then the board: new wrapper (thin!) + openXC7 + NetBSD demo
   re-run on the composed bitstream.

## Files
- Loom/Hw/Rename.lean (traversals), Loom/Hw/Compose.lean (combinators),
  Machines/Lnp64mini/HpMaster.lean, GpMaster.lean, Soc.lean,
  fpga/zc702/lnp64mini_soc_top.v (thin wrapper), tb_lnp64mini_soc.v.
- lake build + audit green at every step; existing lnp64mini files
  untouched (Soc composes the existing design value).

## Deviations (recorded 2026-07-30)

1. **GP master prefix is `gpm_`, not `gp_`.** The lnp64mini core already
   owns input coordinates `gp_done`/`gp_rdata`/`gp_busy` and registers
   `gp_rd`/`gp_wr`/`gp_addr_r`/`gp_wdata_r`. Prefixing the GP master with
   `gp_` would make its status registers collide with the core's GP-response
   inputs under `par` (`parOkB` rejects it). Prefix `gpm_` keeps the two
   disjoint; the connect wiring maps core `gp_done ← gpm_done`, etc. The HP
   master keeps prefix `hp_` (no collision: core's HP inputs are `m_*`).
   Soc top ports are therefore `gpm_m_awready`… and the wrapper/PS7 wiring
   uses those names.

2. **The masters' `m_rdata` response input is named `m_rdata_in`** (→
   `hp_m_rdata_in`, `gpm_m_rdata_in`). The Verilog port is `m_rdata`, but
   the emitter turns every *register* into an `o_<name>` output and every
   *input* into a bare `input wire <name>`; a `.reg`-input named `m_rdata`
   would shadow nothing here, but the mini core already uses `m_rdata` for
   ITS response input, so the distinct `_in` suffix keeps intent legible and
   avoids any future co-emission ambiguity. The tb/wrapper drive
   `hp_m_rdata_in`.

3. **`dbg_state` is a registered mirror, not a combinational alias.** The
   Verilog `assign dbg_state = st;` is combinational; Loom registers have no
   combinational output aliases, so `dbg_state` is a register updated
   `dbg_state <= st` (one cycle late). Observability only; no functional
   effect. Same choice would apply to the constant AXI qualifiers, which are
   registers with a fixed reset value and no writes.

4. **AXI constant qualifiers (`m_awlen`/`m_awsize`/… ) are fixed-init
   registers.** The Verilog drives them with `assign` constants. As Loom
   registers they carry the constant as their reset `init` and are never
   written, emitting as fixed `o_*` ports the thin wrapper feeds to PS7.

5. **soc tb cycle count matches the old tb exactly (273).** The spec warned
   the AXI-slave latency might differ; in practice the behavioral AXI3 slave
   here lands on the same total latency as the old behavioral-DDR tb, so
   cycles=273 as well. All architectural values match exactly.
