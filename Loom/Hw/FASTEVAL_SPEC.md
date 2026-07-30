# FastEval — the verified fast evaluator (spec, representation choices, deviations)

Status of this document: written before the implementation, updated at the
end of the work session with the measured numbers and the final proof
status.  It is the deviations note the task asked for.

## 1. The limitation being removed

`Loom/Hw/Semantics.lean` models design state with

```lean
def RegEnv := String → (w : Nat) → BitVec w
def MemEnv := String → Nat → (w : Nat) → BitVec w
```

`RegEnv.set` returns a *closure* that captures the previous environment, so
after `n` writes a single register read walks an `n`-deep chain of string
comparisons.  Consequently `Design.run` costs `O(cycles² × regs)` and is
unusable as an oracle beyond a few hundred cycles (see the comment on
`Machines/Substrate/S13Soak.lean:selftest`, which caps the lockstep at 400
cycles for exactly this reason).

The practical consequence is that every Loom machine has to be written
**twice**: once as a `Design` (the thing that is compiled and proved about)
and once as a hand-written ISS (the thing that is fast enough to produce
silicon oracles).  The two are cross-checked only at shallow depth.
`FastEval` removes that: the `Design` itself becomes the fast oracle.

## 2. Representation choices

### 2.1 Values: masked `Nat`

`FastSt` stores register and memory contents as `Array Nat`, each entry
already reduced modulo `2^width` (the invariant `Agree` below pins this
down: entry `i` equals `(σ.regs name_i width_i).toNat`).

*Why `Nat` and not `BitVec`?*  Widths are heterogeneous, so a `BitVec`
array would need either a Σ-type (boxing + a width field per cell) or a
uniform maximum width.  `Nat` is the natural erasure: `BitVec w` *is*
`Fin (2^w)`, so `.toNat` is a projection and every `BitVec` operation has a
`toNat` characterisation in core (`BitVec.toNat_add`, `toNat_and`,
`toNat_not`, …).  That makes the correctness proof a direct structural
induction with one core lemma per operator, and it keeps the evaluator
total for any width.

*Cost:* values with width ≥ 64 leave Lean's small-`Nat` (unboxed, ≤ 2^63)
range and use GMP.  Every design in `Machines/Substrate` is ≤ 32 bits and
therefore fully unboxed.  A `UInt64` specialisation for `w ≤ 64` is
recorded as future work (it would add a `UInt64.toNat` layer to every proof
obligation for a constant-factor win).

### 2.2 Registers and inputs: one contiguous index space

`regList d = d.regs.map (name,width) ++ d.inputs.map (name,width)`.
Inputs are read with `Expr.reg` (D15), so they simply live at the end of
the same index space; `fastCycleOpen` writes the input coordinates by index
before cycling, mirroring `St.setInputs`.

### 2.3 Memories: one flat array with per-memory bases

`FastSt.mems : Array Nat` holds every memory concatenated, memory `k`
occupying `[memBase d k, memBase d k + 2^addrWidth_k)`.  A flat array (as
opposed to `Array (Array Nat)`) avoids the nested-update aliasing that
would copy an inner array on every write, and it turns the "a write to one
memory does not disturb another" side condition into one arithmetic
disjointness lemma (`memBaseOf_step` / `memBase_inj`) instead of a
nesting argument.

Bases, sizes and widths are *inlined into the elaborated expression nodes*
(`FExpr.memRead base`), so evaluation needs no metadata lookup at all —
`FExpr.eval` sees only the two flat arrays.

### 2.4 Expressions: width-erased op tree with pre-resolved indices

`FExpr` mirrors `Expr` but is not width-indexed: each node carries the
constants its `Nat` semantics needs (`mask = 2^w - 1` for `not`, `m = 2^w`
for `add`/`sub`/`shl`, the source width's sign bit for `slt`, …), and
`Expr.reg name` has become `FExpr.reg i`.  So no `String` ever appears in
the hot loop.

Two operators are *guarded* relative to the naive `toNat` formula, purely
so that a hostile shift amount cannot allocate a gigantic `Nat`:

* `shl`: `if vb < w then (va <<< vb) % 2^w else 0`
* `shr`: `if vb < w then va >>> vb else 0`

Both guards are proved equal to the unguarded `BitVec` semantics
(`FastEval.shiftLeft_mod_eq_zero`, `FastEval.shiftRight_eq_zero`).

### 2.5 Elaboration is a plain total function

`Design.elaborate` uses list lookups (`regIdx`, `memIdx`) — no hash map, no
`unsafe` pointer memoisation, no `implemented_by`.  This keeps the audit's
trust surface unchanged (the audit whitelists `implemented_by` per
declaration, and FastEval adds none).  Elaboration walks the `Expr` term as
a *tree*, so a design whose Lean term has heavy DAG sharing pays for that
sharing once, at elaborate time; every cycle afterwards is free of it.

## 3. The correctness statement

The honest statement is *per coordinate*, not extensional equality of
`St`s: `toSt` cannot recover the junk values `RegEnv` holds at undeclared
names and off-widths, and nothing observes them.

```lean
structure Agree (d : Design) (fs : FastSt) (σ : St) : Prop
theorem fastCycle_eq (d : Design) (h : d.fastWFB = true)
    (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (fastCycle d.elaborate fs) (d.cycle σ)
```

with

* `ofSt d σ` building a `FastSt` for which `Agree d (ofSt d σ) σ` holds by
  construction (`agree_ofSt`),
* `fastReset d = ofSt d d.reset`, hence `Agree d (fastReset d) d.reset`,
* `fastRun_eq` : `Agree d (fastRun fd n fs) (d.run n σ)` by induction,
* `fastCycleOpen_eq` / `fastRunOpen_eq` for the open (D15) case,
* `Agree.peekReg` / `Agree.peekMem` : the readback of any *declared*
  coordinate agrees, which is what an oracle actually consumes.

**Proof status: PROVED.**  No `sorry`, no new axiom, no `native_decide`; the
whole file's closure is `[propext, Classical.choice, Quot.sound]`.

`d.fastWFB` is the decidable side condition (Bool, `O(design)`, no
`decide` in the kernel): register/input names distinct, memory names
distinct, every `Expr.reg` read resolves to a declared coordinate *at the
read width*, every `Act.write` likewise, every memory access uses the
declared data width and an address expression no wider than the declared
address width.  All four `Machines/Substrate` designs discharge it **in the
kernel** with `by rfl` (`design_fastWF`), so `fastRun_eq` /
`fastRunOpen_eq` apply to them as instantiated theorems
(`S13Soak.fastRun_agrees`, `S0BscanRegs.fastRunOpen_agrees`) — the printed
oracle numbers are a theorem about `Design.run`, not merely a corroborated
computation.

## 4. Corroboration harness

Independently of the proof, `Loom/Hw/FastEval.lean` exposes
`Design.lockstep`, a randomised + directed differential harness that runs
`fastCycle` and `Design.cycle` side by side at small depth and compares
every declared coordinate (registers *and* memory cells), optionally under
a pseudo-random input trace (`randomInEnv`).  It is run for all four
Substrate designs by `lake exe fastbench lockstep`, and per-design from
`lake env lean --run Machines/Substrate/Emit.lean selftest`.

## 5. What got demoed

* `Machines/Substrate/S13Soak.lean` — `selftest` now uses `fastCycle` as the
  oracle (unbounded depth), and `fastVsIss` checks the **full K = 100000**
  run of the fast evaluator against the hand ISS on every register.  The
  hand ISS is kept only as the (now redundant) second opinion; the numbers
  it and `fastCycle` agree on are the ones read back from ZC702 silicon.
* `Machines/Substrate/S0BscanRegs.lean` — `fastVsIss` replays the
  acceptance trace through `fastCycleOpen` and compares against the ISS
  after every command (registers *and* BRAM).
* `Machines/Substrate/S1Counters.lean` — a new small design written with
  the Part-B ergonomics (`Reg`/`RegArray` handles, `act!`/`⇐` notation,
  `Loom.Hw.Trees`), emitted and iverilog-smoked.

## 6. Part B — notation, handles, trees

* `Loom/Hw/Notation.lean` — `Reg w` / `RegArray w n` typed handles with
  `.rd`, `.set`, `.decl`, `.input`, `.dynRd`, `.dynSet`, `.any`, `.sum`;
  `Expr` operators via `scoped instance`s (`+ - &&& ||| ^^^ ~~~ <<< >>>`,
  `OfNat` so `1`/`0xFFF` are literals) plus `===`, `<ᵤ`, `<ₛ`,
  `c ?? t ::: f`; `Act` notation (`r ⇐ e`, `a ;; b`, `when c then a`,
  `unless c then a`, `ifA c then t else e`, `act! { … }`, `rule! n => a`).
  Standard `notation`/`macro` only — no elaborator plugins, and everything
  is `scoped` so no existing machine is affected.
* `Loom/Hw/Trees.lean` — `pairFold`, `reduceTree`, `orTree`, `addTree`,
  `priTree`, `priTreeLast`, `actPriTree`, `dynWrite`, moved out of
  `Machines/Lnp64mini/Core.lean` (which keeps its own copies until its
  owner migrates it) **with proved evaluation lemmas**:
  `reduceTree_eval_or`, `reduceTree_eval_add`, `priTree_eval`,
  `actPriTree_run`.

## 7. Deviations from the task statement

1. `toSt (fastCycle …) = d.cycle σ` is *not* provable as stated (junk
   coordinates), so the theorem is the per-register `Agree` formulation the
   task offered as the alternative.  `toSt` is still provided, and
   `Agree.peek` gives the extensional consequence on declared coordinates.
2. **The perf target is met at Substrate scale but not at lnp64mini scale.**
   `Design.elabExpr` walks the Lean `Expr` term as a *tree*, so the DAG
   sharing that the Verilog emitter recovers (via its pointer-memoised
   `compileExprFast`) is expanded: `lnp64mini` elaborates to 125 075
   nodes/cycle, and 100 k cycles take ~41 s compiled (~2 400 cycles/s) —
   fast, correct, and ~10^6× better than `Design.run`, but not "seconds".
   The identified fix is the *array-encoded* form the task also offered: a
   `FProg : Array FNode` where each node's children are indices into the
   same array (all strictly smaller), built by hash-consing at elaborate
   time, with `evalProg` filling a value array in index order.  Its
   correctness is a strong induction on the index under the invariant
   "wire `i` denotes `FExpr` `e_i`", plus a soundness obligation on the
   hash-cons memo — a bounded but real proof that did not fit this
   session.  Recorded as the next step; the tree evaluator's theorem is
   unaffected by it (`FProg` would be an additional, separately-verified
   layer).
3. Part B's application to `Core.lean` is deliberately not done (that file
   is owned elsewhere); the infrastructure plus a fresh demo design is
   delivered instead, as instructed.

## 8. Measurements

Compiled (`lake exe fastbench scale`, `Tools/FastEvalBench.lean`):

| design | scale | fastCycles | time |
| --- | --- | --- | --- |
| `s13soak` | 29 regs, 32 rules, ~2 k nodes/cycle | 10 000 | 19 ms |
| `s13soak` | " | **100 000** | **185 ms** |
| `s13soak` | " | 1 000 000 | 482 ms (frozen after K) |
| `lnp64mini` | 273 regs, 9 rules, 4 mems, 125 075 nodes/cycle | 100 000 | 41 180 ms |

Interpreted (`lake env lean --run`): `s13soak` 100 000 cycles in 10.5 s.

For contrast, the reference `Design.run` needs **1 314 ms for 400 cycles**
of the same design, and is quadratic: 100 000 cycles would be on the order
of a day.  `lnp64mini` elaboration itself is 1 125 ms (interpreted) and
`fastWFB = true`.

Cross-checks (all green):

* `lake exe fastbench lockstep` — `fastCycle` ≡ `Design.cycle` on
  `s0blinky` (300), `s13soak` (300), `s0bscan` (60 cycles, randomised input
  trace), `s1counters` (300), comparing every register and memory cell each
  cycle.
* `lake env lean --run Machines/Substrate/Emit.lean selftest` —
  `S13SOAK FAST≡ISS OK depth=100008 (all 29 regs)`,
  `S0BSCAN FAST≡ISS OK (33 cmds, regs + BRAM)`, plus both reference
  lockstepss and `S1COUNTERS LOCKSTEP OK`.
* `scripts/s1counters_demo.sh` — iverilog RTL == `fastCycle` prediction
  over 512 cycles on all 15 registers.

`lake exe audit`: all checks passed; 17 unsafe declarations and 4
`implemented_by` replacements, i.e. **unchanged** — FastEval, Trees and
Notation add zero trust surface.
