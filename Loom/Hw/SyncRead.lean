-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Std.Data.HashMap
import Loom.Hw.Syntax
import Loom.Hw.Semantics

/-!
# D19 — sync-read memories are a decidable *shape* discipline (L3)

µVerilog has exactly one kind of memory: synchronous write ports and
in-expression asynchronous reads (`mem[addr]`).  On an FPGA that shape is
LUTRAM: a 1024×64 regfile with six read addresses costs thousands of LUT
sites, which is what pinned `lnp64mini_dual` at 93–100 % of an XC7Z020's
`SLICE_LUTX` with 138/140 block RAMs idle.  Block RAM needs a
*registered* read: `always @(posedge clk) rdreg <= mem[addr];`.

**The decision (D19, 2026-07-30): no new syntax, no new semantics, no new
emission path — a decidable check.**  A `Design` already expresses a
registered read: a rule that writes a register with a bare `memRead` as
the whole written value *is* the read register, and the compiler already
emits it as `rdreg <= n_k;` with `wire n_k = mem[n_addr];` inside the one
`always @(posedge clk)` block.  Nothing needs to change for such a design
to be block-RAM shaped; what was missing is a *check* that a memory is
read **only** that way, because a single stray combinational read (or two
read sites the printer's hash-consing fuses into one wire) silently
demotes the whole memory back to LUTRAM.

`Design.syncReadOkB d m` is that check.  It is the D12/D13/D14 pattern:
the obligation is one kernel-reducible Boolean discharged by the concrete
machine, not a proof burden on the framework and not a new constructor
threaded through 24 exhaustive matches.

## What the check demands

For memory `m` of design `d`, `syncReadOkB` is `true` iff

* **(S1) sanctioned position.** Every `Expr.memRead _ m _` node anywhere in
  `d.rules` occurs as the *entire* value expression of an `Act.write` —
  never inside a guard, a larger expression, a `memWrite` address/data, or
  another memory's read address.  (`Act.strayReadsMem` is the negation.)
* **(S2) one register per site, one site per register.** The destination
  register names are pairwise distinct, and each destination register has
  exactly **one** syntactic write site in the whole design
  (`Design.regWriteCount = 1`).  So its compiled next-value expression is a
  mux cone with the `memRead` at exactly one leaf and the register itself
  at every other leaf — a plain clock-enabled read register.
* **(S3) pairwise distinct address expressions.** No two read sites of `m`
  may carry structurally identical address expressions.  This condition is
  the one that is easy to violate by accident and expensive to diagnose:
  the printer hash-conses on rendered form, so two equal addresses share
  **one** `wire n_k = m[n_a];`, that wire then fans out to two read
  registers, and no downstream tool can merge either flop into a read port.
  (yosys's `opt_merge` fuses structurally equal `$memrd` cells for exactly
  the same reason, so keeping the *sources* distinct is what matters.)
  `Expr.key` renders an expression the way the printer does, so
  "distinct keys" is precisely "distinct printer wires".
* **(S4) declared widths.** `m` is declared, and every site's destination
  width is `m`'s `dataWidth`.

## What the check buys (emission argument)

`syncReadOkB` is read by **no semantic function**: not `Expr.eval`, not
`Act.run`, not `Design.cycle`, not `Compile.compile`, not `Module.cycle`,
not the printer.  It is a predicate *about* a design, not a part of one.
Consequently every existing theorem — `compile_cycle`, `compile_cycle_mems`,
`compile_cycleOpen`, `toProgram_denotes`, the A-EV emission theorem, the
round-trip theorem — holds verbatim and is not even re-elaborated: **the
emitted text of a design that passes the check is byte-identical to the
text it had before anyone thought about block RAM.**

What the check certifies is a property of *that unchanged text*.  Under
(S1)–(S4), by inspection of `Compile.nextReg` and `Print.pExprM`:

1. the printer emits exactly `(d.syncReadSites m).length` wires of the form
   `wire [dw-1:0] n_k = m[n_a];`, with pairwise distinct `n_a` (S3), each
   referenced by exactly one register's next expression (S1 + S2);
2. that register's next expression is a mux cone whose only non-`n_k` leaves
   are the register itself (S2 + `nextReg`'s pruning of `ite`s that cannot
   write the register), i.e. a clock-enabled flop fed directly by the
   memory's asynchronous read output;
3. no other occurrence of `m[...]` exists in the module (S1).

(1)–(3) are exactly yosys's `memory_dff` merge pattern: `opt_dff` folds the
self-feedback mux into a `$dffe`, `memory_dff` absorbs the `$dffe` (enable,
and the synchronous reset the printer emits in the `if (rst)` arm) into the
`$memrd` port, and `memory_libmap` then has an all-synchronous memory it can
place in block RAM.

The semantic content of a passing site is unchanged D9: the value latched is
the **pre-cycle** memory content, because `Act.run` evaluates every
expression against `σ`, the pre-cycle state (`syncReadSite_run` below).
That is read-first ("old data") behaviour, which is what a Xilinx BRAM read
port gives for a same-port collision and what the emitted `always` block
means in IEEE 1800 for a cross-port collision.  Cross-port same-address
collisions are indeterminate on Xilinx silicon; a design that can collide
must argue separately that the colliding cycle is unobservable (see
`Machines/Lnp64mini`'s D19 note).

Corroboration that (1)–(3) really is what the tools do lives in the ladder:
the emitted RTL is bit-exact against the ISS in iverilog before and after a
shape change, and `yosys synth_xilinx` reports the RAMB36E1 count.
-/

namespace Loom.Hw

/-! ## Structural keys

`Expr.key` renders an expression exactly the way `Print.pExpr` renders it
(same operator spellings, same width annotations), only as a tree rather
than in SSA form.  Two expressions therefore receive the same key iff the
printer's hash-consing gives them the same wire — which is what (S3) needs
to talk about.  Names are assumed to be identifier tokens (D14's
`moduleNamesOkB` discipline); without that, key equality is coarser than
structural equality and the check is conservative in the wrong direction,
which is why D14's discipline is a standing assumption here too. -/
def Expr.key : {w : Nat} → Expr w → String
  | w, .lit v => s!"({w}'d{v.toNat})"
  | w, .reg _ n => s!"({w}:{n})"
  | dw, .memRead _ m addr => s!"({dw}:{m}[{addr.key}])"
  | w, .and a b => s!"({w}:{a.key} & {b.key})"
  | w, .or a b => s!"({w}:{a.key} | {b.key})"
  | w, .xor a b => s!"({w}:{a.key} ^ {b.key})"
  | w, .not a => s!"({w}:~{a.key})"
  | w, .add a b => s!"({w}:{a.key} + {b.key})"
  | w, .sub a b => s!"({w}:{a.key} - {b.key})"
  | w, .shl a b => s!"({w}:{a.key} << {b.key})"
  | w, .shr a b => s!"({w}:{a.key} >> {b.key})"
  | _, .eq a b => s!"(1:{a.key} == {b.key})"
  | _, .ult a b => s!"(1:{a.key} < {b.key})"
  | _, .slt a b => s!"(1:$signed({a.key}) < $signed({b.key}))"
  | w, .mux c t f => s!"({w}:{c.key} ? {t.key} : {f.key})"
  | _, @Expr.slice _ a lo w' => s!"({w'}:{a.key}[{lo + w' - 1}:{lo}])"
  | w', .zext a _ => s!"({w'}:zext {a.key})"
  | w', .sext a _ => s!"({w'}:sext {a.key})"

/-- Does `e` contain *any* read of memory `m`? -/
def Expr.readsMem (m : String) : {w : Nat} → Expr w → Bool
  | _, .lit _ => false
  | _, .reg _ _ => false
  | _, .memRead _ m' addr => m' == m || addr.readsMem m
  | _, .and a b | _, .or a b | _, .xor a b
  | _, .add a b | _, .sub a b | _, .shl a b | _, .shr a b
  | _, .eq a b | _, .ult a b | _, .slt a b => a.readsMem m || b.readsMem m
  | _, .not a => a.readsMem m
  | _, .mux c t f => c.readsMem m || t.readsMem m || f.readsMem m
  | _, .slice a _ _ => a.readsMem m
  | _, .zext a _ => a.readsMem m
  | _, .sext a _ => a.readsMem m

/-! `readsMem` walks an expression as a *tree*.  The compiler's expressions
are DAGs with heavy sharing (`priTree`, `addTree`, `actPriTree`), so the
reference definition has the same exponential blowup that forced
`Print.pExprM`'s pointer-memoized twin (D13's cost caveat).  The
`implemented_by` twin below gives each pointer-distinct node one visit;
it computes the same Boolean, and only compiled evaluation uses it. -/
private unsafe def readsMemImpl (m : String) {w : Nat} (e : Expr w) : Bool :=
  (go e).run' {}
where
  go : {w : Nat} → Expr w → StateM (Std.HashMap USize Bool) Bool := fun {_} e => do
    let k := ptrAddrUnsafe e
    if let some b := (← get).get? k then return b
    let b ← match e with
      | .lit _ | .reg _ _ => pure false
      | .memRead _ m' addr => do
          if m' == m then pure true else go addr
      | .and a b | .or a b | .xor a b
      | .add a b | .sub a b | .shl a b | .shr a b
      | .eq a b | .ult a b | .slt a b => do
          if ← go a then pure true else go b
      | .not a => go a
      | .mux c t f => do
          if ← go c then pure true else if ← go t then pure true else go f
      | .slice a _ _ => go a
      | .zext a _ => go a
      | .sext a _ => go a
    modify (·.insert k b)
    return b

attribute [implemented_by readsMemImpl] Expr.readsMem

/-- One sanctioned read site: `.write dw r (.memRead dw m addr)`. -/
structure ReadSite where
  /-- Destination (read) register. -/
  reg : String
  /-- Its width, which (S4) must be the memory's `dataWidth`. -/
  width : Nat
  /-- `Expr.key` of the address expression (S3 compares these). -/
  addrKey : String
deriving DecidableEq, Repr

/-- The sanctioned read sites of `m` in an action, in preorder. -/
def Act.syncReadSites (m : String) : Act → List ReadSite
  | .skip => []
  | .seq a b => a.syncReadSites m ++ b.syncReadSites m
  | .ite _ t e => t.syncReadSites m ++ e.syncReadSites m
  | .write w r (.memRead _ m' addr) =>
      if m' = m then [⟨r, w, addr.key⟩] else []
  | .write .. => []
  | .memWrite .. => []

/-- A read of `m` in a position the discipline does not sanction (S1). -/
def Act.strayReadsMem (m : String) : Act → Bool
  | .skip => false
  | .seq a b => a.strayReadsMem m || b.strayReadsMem m
  | .ite c t e => c.readsMem m || t.strayReadsMem m || e.strayReadsMem m
  -- a bare `memRead` as the whole written value is the sanctioned shape
  -- (whichever memory it reads), so only its *address* can still be stray
  | .write _ _ (.memRead _ _ addr) => addr.readsMem m
  | .write _ _ v => v.readsMem m
  | .memWrite _ _ _ _ addr data => addr.readsMem m || data.readsMem m

/-- Number of syntactic `write` sites targeting register `r` (S2). -/
def Act.regWriteCount (r : String) : Act → Nat
  | .skip => 0
  | .seq a b => a.regWriteCount r + b.regWriteCount r
  | .ite _ t e => t.regWriteCount r + e.regWriteCount r
  | .write _ r' _ => if r' = r then 1 else 0
  | .memWrite .. => 0

/-! ## Design-level queries -/

def Design.syncReadSites (d : Design) (m : String) : List ReadSite :=
  d.rules.flatMap fun rl => rl.body.syncReadSites m

def Design.strayReadsMem (d : Design) (m : String) : Bool :=
  d.rules.any fun rl => rl.body.strayReadsMem m

def Design.regWriteCount (d : Design) (r : String) : Nat :=
  d.rules.foldl (fun n rl => n + rl.body.regWriteCount r) 0

/-- **The D19 check.** See the module docstring for (S1)–(S4). -/
def Design.syncReadOkB (d : Design) (m : String) : Bool :=
  match d.mems.find? (fun md => md.name == m) with
  | none => false
  | some md =>
      let sites := d.syncReadSites m
      !d.strayReadsMem m
        && !sites.isEmpty
        && decide (sites.map (·.reg)).Nodup
        && decide (sites.map (·.addrKey)).Nodup
        && sites.all (fun s => s.width == md.dataWidth)
        && sites.all (fun s => d.regWriteCount s.reg == 1)

/-- A human-readable D19 report line for one memory. -/
def Design.syncReadReport (d : Design) (m : String) : String :=
  let sites := d.syncReadSites m
  let regs := String.intercalate "," (sites.map (·.reg))
  s!"  {m}: syncReadOk={d.syncReadOkB m} sites={sites.length} [{regs}]" ++
  (if d.strayReadsMem m then "  (STRAY combinational read)" else "")

/-! ## The semantic content of a read site (D9, restated)

Nothing about D19 changes `Design.cycle`; this lemma just records what a
sanctioned site *means*, which is the fact a block-RAM read port has to
reproduce: the value latched is the **pre-cycle** memory content, evaluated
at the pre-cycle address.  Read-first, never write-first. -/
theorem syncReadSite_run (σ acc : St) (m r : String) {dw aw : Nat}
    (addr : Expr aw) :
    ((Act.write dw r (Expr.memRead dw m addr)).run σ acc).regs r dw
      = σ.mems m (addr.eval σ).toNat dw := by
  simp [Act.run, RegEnv.set, Expr.eval]

end Loom.Hw
