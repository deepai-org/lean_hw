# Lnp64mini → Loom porting spec (the architecture decisions)

Spec source: `/home/ubuntu/remote-fpga/fpga/substrate0/rtl/lnp64mini3_regs.v`
(685 lines — THE reference; port it bug-for-bug, NBA semantics = D9).
Pattern files (validated on silicon): `Machines/Substrate/S13Soak.lean`
(closed engine, per-element regs, ISS mirror), `Machines/Substrate/S0BscanRegs.lean`
(open design, cmd ports, acceptance trace), `Loom/Hw/DESIGN.md` §D15.

Goal chain: Lean `Design` (this port) → emit → iverilog vs Lean ISS →
ZC702 vs Rust emulator → the §61 NetBSD-over-GEM demo on the Loom core.

## Module layout

- `Machines/Lnp64mini/Core.lean` — the `Design` (name "lnp64mini") + Expr
  shorthands. Built with `Fin`-indexed builder functions like Lnp64u.
- `Machines/Lnp64mini/Iss.lean` — cycle-accurate FSM mirror (`MiniSt`
  structure of BitVecs + `step : MiniSt → MiniIn → MiniSt`), the fast
  oracle. Mirror the always-block top-to-bottom with ALL reads from the
  pre-state (Id.run do + s' pattern of `SoakIss.step`).
- `Machines/Lnp64mini/Harness.lean` — DDR model (Std.HashMap Nat (BitVec 64),
  configurable read latency), system stepper (core ISS + DDR model +
  EDSL `cycleOpen` variant), test programs, `selftest` (EDSL ≡ ISS, small
  depth), `progtest` (ISS runs programs to halt; print arch state).
- `Machines/Lnp64mini/Emit.lean` — root `main` shim (NOT in the umbrella):
  emit `rtl/lnp64mini.v`, run selftest/progtest.
- Add Core/Iss/Harness imports to `Machines.lean`; Emit stays out.

## Constants (from the Verilog)

ID_MAGIC=0x53301017 (Loom edition of 0x53300017 — wrapper serves it, not
the design). TEXT_BASE=0x1000, PROG_BASE=0x20000000 (unused in v2),
DATA_BASE=0x10000000, UART_ADDR=0x8000, UART_RX_ADDR=0x8008. NT=32, CW=5,
AW=10. FSM states S_IDLE=0 … S_GPS=20 exactly as the localparams.

## D15 input ports

  m_done 1, m_rdata 64, m_busy 1        (HP master handshake)
  gp_done 1, gp_rdata 32, gp_busy 1     (GP master handshake)
  cmd_valid 1, cmd_idx 7, cmd_data 32   (BSCAN write surface = wr_pulse/
                                         wr_addr_j/wr_data_j, one pulse per
                                         JTAG write transaction)

All other mini3 module ports are wrapper business (AXI wiring, DRCK/UPDATE
domains, heartbeat, fclk).

## State mapping (name / kind / note)

Loom mems (single-write-port each — see "write funnels"):
- `rf`   aw=10 dw=64 — THE regfile. ONE syntactic memWrite (funnel below).
- `dmem` aw=9  dw=64 — zero page. ONE memWrite via the registered
  dmem_we/dmem_a/dmem_wd (mini3 writes it NONblocking → the write lands
  the cycle after scheduling — keep regs dmem_we/dmem_a/dmem_wd and one
  rule `.ite dmem_we (memWrite …) .skip`, plus `dmem_rd <= memRead dmem
  dmem_a` every cycle. FAITHFUL including the 1-cycle delay).
- `uart_mem` aw=8 dw=8 (one write site: UART store in S_EX; funnel regs
  like dmem: uw_we/uw_a/uw_d? mini3 writes it BLOCKING-in-always? No —
  `uart_mem[uart_wptr[7:0]]<=b[7:0]` nonblocking, single site → model as
  one guarded memWrite directly in the S_EX store-UART rule).
- `rx_mem` aw=8 dw=8 (one write site: cmd 19).

Per-element register arrays (dynamic multi-site writes — mems would need
multiple ports; use `Fin 32` builders, names `tpc0..tpc31` etc.):
- `tpc` 64, `tstate` 2, `tsleep` 64, `tfutex` 64, `tp_arr` 64,
  `sigmask_arr` 64.

**Superseded for four of the six by D20 (2026-07-31) — see deviation 6 and
`DUAL_SPEC.md` §D20.** `tpc`, `tsleep`, `tp_arr` and `sigmask_arr` are now
32x64 Loom **memories** (async `memRead`s, LUTRAM); only `tstate` and
`tfutex` remain per-element, because those two are read at *every* index at
once (priority encoders / the `FUTEX_WAKE` comparator bank).

Scalar registers (width, init) — port ALL of these verbatim:
cur 5/0, pc 64/0x1000, retire 32/0, running 1/0, halted 1/0, st 5/0,
ir 64/0, a 64/0, b 64/0, rdval 64/0, sel_t 64/0, sel_f 64/0,
mem_is_store 1/0, trap_active 1/0, trapped_op 8/0,
core_rd 1/0, core_wr 1/0, core_addr 32/0, core_wdata 64/0,
jtag_rd 1/0, jtag_wr 1/0, jtag_wdata 64/0, ddr_addr_j 32/0, ddr_lo_j 32/0,
ddr_rd_l 64/0, ddr_q 64/0, bus_req 1/0,
gp_rd 1/0, gp_wr 1/0, gp_addr_r 32/0, gp_wdata_r 32/0,
dmem_we 1/0, dmem_a 9/0, dmem_wd 64/0, dmem_rd 64/0,
uart_wptr 9/0, uart_ridx 8/0, uart_byte 8/0 (NEW: latched
  `memRead uart_mem uart_ridx` every cycle → o_uart_byte for the wrapper),
rx_wptr 9/0, rx_rptr 9/0, rx_byte 8/0 (NEW: latched `memRead rx_mem
  (slice rx_rptr 0 8)` every cycle → the UART_RX load uses the LATCHED
  value? NO — see "UART RX fidelity" below),
ld_boff_q 3/0, ld_op_q 8/0, ld_rd_q 5/0,
lr_addr 64/0, lr_valid 1/0, futex_exp 64/0, futex_addr_q 64/0,
sleep_scan 5/0, next_ready 5/0, free_slot 5/0, has_free 1/0,
clone_dst 5/0, clone_tid 5/0,
mul_acc 128/0, mul_aw 128/0, mul_b 64/0, mul_kind 2/0,
div_rem 64/0, div_quo 64/0, div_d 64/0, div_cnt 7/0,
div_isrem 1/0, div_negq 1/0, div_negr 1/0,
zeroing 1/0, zctr 10/0,
reg_sel 5/0, reg_wsel 5/0, reg_wlo 32/0, dmem_addr_j 32/0, dmem_lo_j 32/0,
reg_rd 64/0 (NEW: latched `memRead rf {cur,reg_sel}` every cycle →
  o_reg_rd replaces mini3's DRCK-domain rv0/rv1 sampling).

NOT ported (wrapper): heartbeat, hb0/1 and all DRCK snapshot pairs, the
41-bit DR, wr_tog sync chain, rstc/local_rstn (wrapper drives `rst`),
axi masters, hp mux wires (wrapper computes hp_core_owns from o_running/
o_st and muxes o_core_*/o_jtag_* into the real axi_hp_master).

### UART RX fidelity

mini3's UART_RX load reads `rx_mem[rx_rptr[7:0]]` combinationally in S_EX.
In Loom that's a plain `memRead rx_mem (slice rx_rptr 0 8)` inside the
S_EX rule — allowed (async read)! Use memRead directly; no rx_byte
latch needed. Same for FUTEX_WAKE's tfutex reads (per-element regs) and
the priority encoders. `reg_rd`/`uart_byte` latches are only for the
BSCAN readback surface (stability across the wrapper CDC).

### next_ready / free_slot (registered priority encoders)

Every cycle (unconditional rules, matching the Verilog's registered
always):
- ready bit i = `eq tstate_i 1`; free bit i = `eq tstate_i 0`.
- rbm2 = `(zext readyBm 64 ||| (zext readyBm 64 <<< 32)) >>> zext(cur+1)`
  where readyBm : Expr 32 assembled by or/shl of the 32 bits.
- nr_off = DOWNWARD scan: `foldr` over i = 31…0 of
  `mux (slice rbm2 i 1) (lit i%32… careful: Verilog nr_off=pi[4:0], scan
  pi=63? NO: pi<NT over rbm2[pi] with pi 0..31 — the low 32 bits only) —
  mirror exactly: for pi=31 down to 0: if rbm2[pi] then nr_off=pi (so the
  LOWEST set bit wins — the loop runs high→low, last assignment wins →
  lowest index). Build with foldr from i=0 upward … just replicate: fold
  over [31,30,…,0] with mux(bit pi, lit pi, acc) NESTED so position 0 is
  OUTERMOST mux → lowest set bit wins.
- nr_any = or-reduce of rbm2[31:0].
- next_ready' = mux nr_any (cur + 1 + nr_off) cur  (5-bit add wraps ✓).
- free_slot' = lowest free index (same downward-scan pattern over
  free_bm), has_free' = or-reduce.

### The rf write funnel (THE critical structure)

mini3 funnels every rf write through blocking temps + one write:
`if (rf_we) rf[rf_wa]<=rf_wd`. Loom mirror: ONE rule containing ONE
`memWrite rf port0` guarded by `rfWeE` with address `rfWaE`, data `rfWdE`,
where the three Exprs are priority mux-chains replicating EXACTLY the
assignments along the always block's control flow, in this priority order
(later blocking assignment wins → build the mux with LATER sites OUTER):
1. zeroing (we=1, wa=zctr, wd=0)
2. cmd 52 (reg_wsel≠0): wa={cur,reg_wsel}, wd={cmd_data,reg_wlo} — note
   this fires on cmd_valid ∧ idx=52 even while zeroing (later in block →
   wins over zeroing that cycle; mirror mini3: the case executes AFTER
   the zeroing if — actually zeroing sets rf_we first, wr_pulse case
   comes later and OVERWRITES → cmd wins. Replicate.)
3. the FSM writes (running ∧ ¬halted ∧ ¬zeroing), one per state/branch:
   S_EX: is_sel (sel_cond?sel_t:sel_f→rdf), GET_PCR Tid (cur+1→rdf),
   is_alu (alu→rdf), JAL/JALR (pc8→rdf), CLONE has_free (b→{free_slot,2})
   / no-free (-1→rdf), SC ok (0→rdf)/fail (1→rdf), UART_RX load, S_L1
   load-wb, S_DST load-wb, S_CLONE2 (child sp→{clone_tid,31}),
   S_CLONE3 (tid+1→{cur,clone_dst}), S_MUL done, S_DIV done, S_GPL done.
   These are mutually exclusive by st/op, so ordering among them is free;
   guard each precisely.
Write the funnel as a Lean list of (guard, wa, wd) triples folded into
the three Exprs — keeps it reviewable against the Verilog.

All rd≠0 guards (`rdf ≠ 0` etc.) are part of the write guards. r0 reads
return 0 via the explicit `(rs1f==0)?0:rf[...]` muxes in S_RD — port those
as mux(eq rs1f 0, 0, memRead rf {cur,r1a}).

## Rule order (mirror the always block exactly)

The Verilog is ONE always block; Loom rules in the same textual order,
last-write-wins reproduces the blocking/nonblocking mix as analyzed:
1. `enc` — next_ready/free_slot/has_free updates (they're a SEPARATE
   always block in mini3, order-independent).
2. `sleepdec` — tsleep serialized scan (guarded running∧¬halted):
   sleep_scan+=1; per-element i: if sleep_scan==i ∧ tstate_i==SLEEP then
   (tsleep_i<=1 ? tstate_i:=READY : tsleep_i-=1).
3. `latches` — reg_rd/uart_byte/dmem_rd latch rules.
4. `pulse_defaults` — dmem_we<=0, core_rd<=0, core_wr<=0, jtag_wr<=0,
   jtag_rd<=0, gp_rd<=0, gp_wr<=0 (defaults; later rules override).
5. `zeroing` engine rule (zctr/zeroing updates; rf write handled in
   funnel).
6. `cmd` rules — the wr_pulse case (indices 13,14,15,16,17,18,19,40,41,
   42,43,50,51,52,53,54,55). NOTE these must come AFTER the FSM rules'
   defaults would be… mini3 order: wr_pulse case is BEFORE the FSM case
   in the block, but FSM assignments are NONblocking so order within the
   block doesn't matter except for the blocking rf temps (handled in the
   funnel priority). Keep cmd rules here; exceptions where both cmd and
   FSM write the same reg in one cycle (pc via 53, st via 54 vs FSM):
   in mini3 the FSM's nonblocking write would WIN (later in block? both
   nonblocking → LAST executed wins → the FSM case is later → FSM wins).
   Replicate by putting cmd rules BEFORE the FSM rules. (In practice the
   host never races these; fidelity anyway.)
7. `ddr_rd_l` latch: if m_done ∧ ¬hp_core_owns then ddr_rd_l<=m_rdata,
   where hp_core_owns = running ∧ st∉{S_TRAP,S_WAIT,S_PAUSE} as an Expr.
8. FSM rules, one per state (guard: running ∧ ¬halted ∧ ¬zeroing ∧ st==X),
   each a .seq of guarded writes mirroring that state's branch tree.
   S_EX is big: split into helper `Act`s per opcode group (Lean defs),
   composed with nested .ite in the SAME priority order as the if-chain.
9. `reset_local`: mini3's `if (!local_rstn) …` is the wrapper POR —
   covered by Design reset values; the cmd-13 reset covers soft reset.
   DO port cmd-13 exactly (running/halted/st/pc/uart ptrs/trap/cur/lr/
   zeroing:=1/zctr:=0 + per-element tstate_i := (i==0?READY:FREE),
   tpc_i := TEXT_BASE).

Decode/ALU/branch/imm combinational wires → plain Lean `def`s returning
Expr (imm_i/imm_s/imm_j sign-extended via .sext of slices; alu as a
per-opcode Expr selected by the op mux chain — build `aluE : Expr 64`
mirroring the case; CTZ = downward scan mux chain; ROL/ROR via
shl/shr/or with 6-bit amounts, note the `6'd0 - b[5:0]` wrap trick).

## The ISS (Iss.lean)

`structure MiniIn where mDone : Bool; mRdata : BitVec 64; gpDone : Bool;
gpRdata : BitVec 32; cmdValid : Bool; cmdIdx : Nat; cmdData : BitVec 32`
(busy inputs only surface in status reads — include mBusy/gpBusy : Bool
for completeness). MiniSt = every register above + `rf : Array (BitVec
64)` (1024) + `dmem : Array (BitVec 64)` (512) + uartMem/rxMem arrays +
per-element arrays as `Array`. `step` mirrors the always block WITH THE
SAME pre-state discipline (read `s`, build `s'`; blocking rf temps become
local `mut rfWe/rfWa/rfWd` exactly like the Verilog). Selftest compares
EVERY register + touched mem entries after each cycle for a directed
input script (~200 cycles covering: cmd reset/start, fetch (mDone
pulses), an ALU op, a zp store/load, a DDR load (S_DL/S_DST), branch,
MUL, DIV, EXIT halt). Use `Design.cycleOpen` on the EDSL side.

## Verification ladder (after EDSL≡ISS)

1. `progtest`: hand-encoded programs (instruction format:
   op[63:56] rd[55:51] rs1[50:46] rs2[45:41] rs3[40:36] rs4[35:31];
   imm_i=ir[45:14] sext, imm_s=ir[40:9] sext, imm_j=ir[50:19] sext;
   LI = op 0x02? NO — check: 0x02 alu=a?? LI is op… mini3 has no LI: 
   constants come via a0 ADDI imm with rs1=r0 and LIU 0x04 for the high
   half. Encode: ADDI rd, r0, imm (op 0xa0), LIU (0x04) rd,rs1,imm32.
   Program: compute, store to dmem zp, EXIT (0x3a). ISS runs with a DDR
   model holding the program at DATA_BASE+pc (image[word] ↦ m_rdata with
   1-cycle mDone latency).
2. iverilog: tb instantiates emitted lnp64mini + behavioral DDR array +
   cmd driver (reset, start), runs the same program, compares final
   dmem/rf/pc/retire vs ISS dump. (rf/dmem are module-internal arrays —
   read them hierarchically `dut.rf[i]` like tb_lnp64u does.)
3. Rust emulator cross-check: the SAME program as a flat image via
   `~/lnp64 target/release/lnp64` runners — architectural equality at
   halt (rf via dumps / dmem values via stores).
4. Board: wrapper + openXC7 + jtag_lib (existing register map!) — run
   program from PS DDR (fastload), read rf/dmem/retire over BSCAN.
5. The rump/NetBSD image (the demo).

## Build discipline

- `lake build Machines.Lnp64mini.Core` etc. after each increment; keep
  `lake exe audit` green (no sorries outside Theorems/, no new axioms).
- NO `design_wf` by `decide` yet — the design is huge; skip the theorem
  entirely (goal waives theorems). Emission does not require it.
- Emit via `Design.emit`; expect a multi-MB .v (Lnp64u is 8.7 MB).
- Iterate: never move to the next FSM state until selftest covers the
  current one.

## Deviations (recorded during the port)

1. **Selftest structure = focused per-script lockstep windows, not one
   ~200-cycle script.** The EDSL `Design.cycleOpen` builds a closure-based
   `RegEnv` that grows each cycle, so deep runs are super-linear (the same
   quadratic noted in `S13Soak.selftest`). At ~250 registers per cycle the
   full-program lockstep gets expensive fast (40 cyc ≈ 70 s). The selftest
   therefore runs a *battery* of short directed programs, each started from
   `design.reset` via a single cmd-13 **start** pulse (bit1 only) that
   SKIPS the 1024-cycle zeroing sweep — rf/dmem are already zero at reset,
   tstate0=READY, pc=TEXT_BASE, so the FSM runs immediately and faithfully.
   Each script's window is sized to reach its distinctive states (DDR
   S_DL/S_DST/S_DSW, LR/SC, UART, CLONE/YIELD/THREAD_EXIT, SLEEP+scan+
   S_WAIT, GP S_GPL/S_GPS, ALU/MUL/SEL/GET_PCR/zp/branch/JAL). The FULL
   programs (incl. the 64-cycle MUL/DIV loops and the trap+RESUME service
   flow) are exercised on the fast ISS in `progtest`; the deep EDSL≡RTL
   corroboration is delegated to iverilog (the emitted .v compiles clean
   under `iverilog -tnull -Wall`) per the verification ladder. The cmd
   reset (idx 13 bit0) + zeroing engine + rf/dmem zeroing ARE ported and
   run in the ISS; they are simply not in the hot lockstep loop.

2. **FUTEX_WAKE (`wk` blocking loop) → per-element "matches-before-i <
   count" guards.** mini3 uses a blocking `wk=wk-1` accumulator inside a
   for-loop to wake the first `count` matching FUTEX threads. Loom rules
   have no cross-element blocking accumulator, so element i is guarded by
   `tstate_i==FUTEX ∧ tfutex_i==rdval ∧ (#matches at j<i) < a`, computed as
   a nested `add` of the earlier match bits. Same net effect: the lowest-
   indexed matching threads wake, up to `a`. (Recorded per spec §State
   mapping which anticipated this.)

3. **No `design_wf` theorem** — deliberately skipped per the goal (the
   design is huge; `decide` is infeasible and emission does not need it).
   `lake exe audit` is green regardless (no sorry / no new axioms /
   no native_decide / no source partial).

4. **`m_busy`/`gp_busy` inputs** are declared and threaded through the ISS
   for completeness but never affect core state (mini3 only surfaces them
   in BSCAN status reads, which live in the wrapper). Kept as inputs so the
   port's port list matches the intended wrapper contract.

5. **D19 sync-read shape: the `rf` read path is restructured (2026-07-30).**
   Two deviations from mini3's `always` block, both value-preserving, made
   so `rf` lands in block RAM instead of LUTRAM
   (`Loom/Hw/D19_SPEC.md`; `Design.syncReadOkB "rf"` now checks it):

   * mini3's *shared, state-muxed* read addresses `r1a = (st==S_RD2) ?
     rs3f : rs1f` and `r2a` are **gone**. `S_RD` reads `rf[{cur,rs1f}]` /
     `rf[{cur,rs2f}]` and `S_RD2` reads `rf[{cur,rs3f}]` / `rf[{cur,rs4f}]`
     directly. In each state the mux was already determined by that state,
     so the latched values are identical; but one shared address net gave
     `a`/`sel_t` a single `rf[...]` expression with fan-out two, which no
     downstream tool can merge into a read port.
   * the `(rsNf == 0) ? 0 : ...` **x0 zero-muxes are deleted**, because
     invariant Z — `rf[{t,0}] = 0` in every reachable state — makes them
     the identity. Z is inductive: `rf.init` is zero, and every one of the
     20 `rfTriples` either writes a low index guarded `≠ 0` (`rdf`,
     `ld_rd_q`, `clone_dst`, `reg_wsel`) or a nonzero literal (`L5 2`,
     `L5 31`), or is the zeroing sweep writing `0`. mini3's own `reg_rd`
     JTAG readback already relied on Z (it never had a zero-mux).

   The **ISS is untouched** and the whole ladder is bit-exact — `selftest`
   compares every register plus `rf[0..64)`/`dmem[0..64)` against the ISS,
   and all six iverilog system testbenches produce byte-identical output
   (same cycle counts, same reservation-kill counts) before and after.

   **Residual hardware obligation (D19's standing caveat).** A block-RAM
   read port and the write port are different physical ports, and Xilinx
   7-series TDP RAM leaves read data indeterminate on a same-address,
   same-cycle collision, where `Design.cycle` says "old data". Per memory:
   * `dmem` — read and write share the *same* address net (`dmem_a`), so
     yosys uses one port in READ_FIRST mode: well defined, no obligation.
   * `rf`, ports `a`/`b`/`rdval`/`sel_t`/`sel_f` — enabled only in `S_RD`
     and `S_RD2`, and no `rfTriples` guard can fire in those states
     (`cmd 52` and the zeroing sweep only run with the core stopped), so
     these ports never collide.
   * `rf`, port `reg_rd`, and `uart_mem` port `uart_byte` — free-running
     latches that *can* collide with a write. Both are read back only over
     BSCAN, both re-latch every cycle, and the readback protocol samples
     them across many cycles (`reg_rd` with the core stopped; `uart_byte`
     only at indices `ridx != wptr`), so a single indeterminate cycle is
     unobservable. This argument is *not* machine-checked and has not yet
     been confirmed on silicon — the board was deliberately not programmed
     in the pass that introduced D19.

6. **D20 — four of the six thread-table arrays are memories (2026-07-31).**
   `tpc`, `tsleep`, `tp_arr` and `sigmask_arr` moved from `Fin 32` register
   banks to 32x64 Loom `MemDecl`s; `tstate` and `tfutex` stayed per-element.
   Rationale, per-array decision table, the `MemWriteWF` port assignment and
   the measured cost are in `DUAL_SPEC.md` §D20. Three points matter here:

   * **Reads are plain asynchronous `memRead`s, not D19 sync-read sites.**
     `memRead` evaluates against the pre-cycle state at the pre-cycle
     address (D9), which is *definitionally* what the 32-way `priTree` over
     32 pre-cycle registers computed. Nothing is restaged, so every
     register keeps its exact cycle-by-cycle value, the ISS needed no
     change on the read side, and the whole ladder — including all six
     iverilog cycle counts — is byte-identical. `syncReadOkB` is `false`
     for all four, deliberately: distributed RAM is the right (and
     collision-free) implementation at 32x64.
   * **The FSM's writes are funnelled** into one new rule `tarr_funnel`
     (`tpcTriples` + three single-site writes), mirroring `rfTriples`, so
     each array has one syntactic `memWrite` and `Compile.MemWriteWF`'s
     ascending-port condition is trivial. `tsleep` is the exception: the
     sleep scan (port 0, rule `sleepdec`) and `S_EX SLEEP` (port 1,
     `tarr_funnel`) can write different indices in the same cycle.
   * **The one real behavioural deviation:** `cmd 13`'s 32-entry `tpc`
     reset became a 32-cycle sweep off the zeroing counter, because a
     memory cannot take 32 writes in one cycle. It is unobservable — every
     `tpc` read is under `fsmEn`, and `fsmEn` contains `¬zeroing` — and the
     ISS mirrors the sweep bit-for-bit.

## Fidelity gap: the scheduler is COOPERATIVE, Law 5 requires preemptive

Recorded 2026-08-01. Every write to `cur` (the current-thread register) in
`Core.lean` is at an explicit yield point — `YIELD` (0x06), `SLEEP` (0x07),
`THREAD_EXIT` (0x3b), the `FUTEX_WAIT` block in `S_FTX1`, and `S_WAIT`'s pick
when the core is otherwise idle — plus `cur := 0` on the cmd-13 reset. There is
**no timer, no quantum, no preemption tick**: a thread runs until it
voluntarily blocks or exits. The serialized sleep scan and the cross-core
doorbell only move threads to READY; neither takes the CPU from the runner.

This is faithful to mini3 (the port's job) but **not** to the architecture:
`lnp64_isa.md` Law 5 says "Every instruction boundary is a preemption point.
Unconditionally. The machine contains no non-preemptible region."

Measured consequence, not hypothetical: in the §64 dual-core work core 1's
worker first paced itself with a spin loop, and because nothing preempts a
spinning thread its instruction fetches took enough arbiter share to starve
core 0's GEM pump to **100 % packet loss**. The fix was software discipline
(one long `SLEEP`, which parks in the scheduler and fetches nothing) because
the hardware has no way to intervene. Cooperative scheduling's failure mode,
observed on silicon.

Why it is adequate today: the rump guest yields constantly (futex waits,
condvar sleeps, the pump's 30 ms nap). It would not be adequate for a hostile
or compute-bound thread — which is exactly what Law 5 exists to rule out.

Closing it looks contained: the per-cycle sleep scan is already a timebase and
`S_F0` is precisely the instruction boundary Law 5 names, so a decrementing
quantum that forces the `S_WAIT`-style switch at `S_F0` would be the shape.
Not attempted here; named so it is not mistaken for architectural fidelity.

**CLOSED 2026-08-02 by EXT-1** (`EXTEND_SPEC.md`, increment log), in exactly
that shape: per-core `quantum`/`qctr` registers loaded over BSCAN **cmd 57**,
the switch forced at `S_F0`, saving `pc` (not `pc8` — at `S_F0` the
instruction has not been consumed). `quantum = 0` is the default and
reproduces everything described above bit for bit, so this section still
describes the machine as shipped until a host writes cmd 57. The spinning
thread that starved the GEM pump is now dislodgeable: `progSpin` in
`Harness.lean` is that failure in nine words, and it terminates only with a
quantum — on the ISS and on the emitted RTL alike.
