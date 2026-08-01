-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Rename

/-!
# Design combinators — the compose layer (D16 candidate)

Three pure total functions over `Design` (ordinary data — no core semantics
changes) plus a decidable `parOkB` runtime guard. Everything additive; the
existing `Design` semantics and every proof about it are untouched.

`compose` idiom (open module `b`'s input `u1_cmd_in` fed from module `a`'s
register `u0_out`):
```
((a.prefixed "u0_").par (b.prefixed "u1_")).connect
  (fun n w => if n = "u1_cmd_in" then some (.reg w "u0_out") else none)
```

## Intended lemma shapes (deferred — see COMPOSE_SPEC.md §Theorems)

* `prefixed`  — bisimulation: `(d.prefixed p)` simulates `d` under the
  name renaming `n ↦ p ++ n`. Reset, `cycleOpen` and observations all
  commute with the injective rename.
* `par`       — product: for disjoint-named `a`,`b`, `(a.par b).cycleOpen`
  factors as `a.cycleOpen` on the `a`-coordinates and `b.cycleOpen` on the
  `b`-coordinates (rule groups touch disjoint state, so the order between
  the two groups is irrelevant).
* `connect`   — input instantiation: `(d.connect wire).cycleOpen ι` equals
  `d.cycleOpen ι'` where `ι'` drives each connected input `i` with the
  same-cycle value `(wire i).eval` of the pre-cycle state (a Verilog port
  connection to a register output — combinational, same cycle).
-/

namespace Loom.Hw

/-! ## `Design.prefixed` -/

/-- Instantiate a design under a namespace: prefix every register, memory
and input name (and every read/write of them, via `mapSignals`) plus every
rule name and the design name with `p`. Instantiation = prefixing. -/
def Design.prefixed (p : String) (d : Design) : Design where
  name := p ++ d.name
  regs := d.regs.map fun r => { r with name := p ++ r.name }
  mems := d.mems.map fun m => { m with name := p ++ m.name }
  rules := d.rules.map fun r =>
    { name := p ++ r.name, body := r.body.mapSignals (p ++ ·) }
  inputs := d.inputs.map fun i => { i with name := p ++ i.name }
  -- D37: an acknowledged undeliverable reset image is acknowledged for the
  -- *instance* too, so the names travel with the prefix.
  ackMemInit := d.ackMemInit.map (p ++ ·)

/-! ## `Design.par` -/

/-- Parallel composition: concatenate the register/memory/rule/input lists.
The caller guarantees disjoint names (use `prefixed`); `parOkB` below is the
decidable guard `Design.emit`-style callers run first. `a`'s rules run
before `b`'s — with disjoint names the order between the two groups is
semantically irrelevant (documented, not yet proven). -/
def Design.par (a b : Design) : Design where
  name := a.name ++ "_" ++ b.name
  regs := a.regs ++ b.regs
  mems := a.mems ++ b.mems
  rules := a.rules ++ b.rules
  inputs := a.inputs ++ b.inputs
  ackMemInit := a.ackMemInit ++ b.ackMemInit   -- D37, carried by both parts

/-- All state/input names a design owns (registers, memories, inputs). The
disjointness a valid `par` needs. -/
def Design.names (d : Design) : List String :=
  d.regs.map (·.name) ++ d.mems.map (·.name) ++ d.inputs.map (·.name)

/-- Decidable runtime guard for `par`: the two designs' owned names are
disjoint (so no coordinate is shared/aliased) and no rule name collides.
Callers (e.g. `Soc`) run this before trusting a `par`. -/
def Design.parOkB (a b : Design) : Bool :=
  let an := a.names
  let bn := b.names
  (an.all (fun n => !bn.contains n)) &&
  (an.eraseDups.length == an.length) &&
  (bn.eraseDups.length == bn.length) &&
  (let ar := a.rules.map (·.name)
   let br := b.rules.map (·.name)
   ar.all (fun n => !br.contains n))

/-! ## `Design.connect` -/

/-- Wire up (some of) a design's inputs from same-cycle expressions over
the composed design's own signals. For each input `i` with
`wire i.name i.width = some e`: drop `i` from the input list and substitute
`e` for every read of `i` in every rule body (`Act.substReg`). `e` is over
the composed design's registers — a combinational, same-cycle Verilog port
connection to a register output.

Inputs the wire function maps to `none` stay as environment inputs (the
soc's real AXI-response + cmd inputs). -/
def Design.connect (d : Design)
    (wire : (n : String) → (w : Nat) → Option (Expr w)) : Design where
  name := d.name
  regs := d.regs
  mems := d.mems
  -- keep only inputs left unwired
  inputs := d.inputs.filter fun i => (wire i.name i.width).isNone
  ackMemInit := d.ackMemInit                   -- D37, unchanged by wiring
  rules := d.rules.map fun r =>
    { r with body :=
        d.inputs.foldl (fun body i =>
          match wire i.name i.width with
          | some e => body.substReg i.name i.width e
          | none   => body) r.body }

end Loom.Hw
