-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireSw

/-!
# R-MC support: the `cap_revoke` mark-engine coupling (design spike)

**Statement-only** (NEXTSTEPS §1.2): the rv-coupling invariant relating
the hidden pointer-doubling registers (`rv_j`/`rv_v`/`rv_r`,
`SysOps.rvInit`/`rvStep`) to descendant marking on the abstraction. No
preservation proofs here yet — this file pins the *shape* so the tier
1–3 arms can't invalidate it silently, and so the eventual `Coupled`
extension is a fill-in.

## The engine, semantically

`rvInit` runs on the first countdown cycle of an in-flight `cap_revoke`
(pre-cycle `if_cl = revokeCost`); each further countdown cycle
(pre-cycle `2 ≤ if_cl < revokeCost`) runs one `rvStep` doubling round.
The tables the engine reads (caps, cells, generations, the issuing
domain's `rs1`) are stable while the instruction is in flight, so the
invariant is stated against the *current* abstraction. With
`k = revokeCost - 1 - if_cl` rounds done:

* `rv_r i = 1` iff a live parent chain of length `< 2^k` from node `i`
  ends in an edge pointing at the revoked root (`reachRootN (2^k)`);
* `rv_v i = 1` iff the `2^k`-step parent chain from `i` exists with
  every edge generation-live (`liveChainN (2^k)`);
* where that chain exists, `rv_j i` indexes its endpoint (`chainEndN`).

At retirement (pre-cycle `if_cl ≤ 1`) `k = revokeCost - 2 = 22` rounds
are done, and `2^22 > numDomains * numSlots`, so `rv_r` has reached the
`Kernel.marks` fixpoint (`marks_eq_reachRootN` below, to be proven with
the retirement arm: `marks root = reachRootN root (numDomains*numSlots)`
pointwise, and `reachRootN` is monotone and saturates at the node
count by acyclicity/pigeonhole).

## Plumbing notes (for the eventual `Coupled` clause)

* Vacuity everywhere else: the guard requires an in-flight `cap_revoke`
  *past its first countdown*. Issue latches `if_cl = revokeCost` (guard
  false), retirement clears `if_v`, non-revoke words fail the opcode
  guard — so only the countdown rule carries proof obligations
  (`rvInit` at `if_cl = revokeCost` establishes `k = 0`; `rvStep`
  advances `k`), and refill/mover/tick preserve it by frames (they
  write neither `rv_*` nor the guard registers nor cap tables).
* The proven `square_countdown` arm needs no change: `abs` ignores
  `rv_*`, and the clause is carried by `coupled_step`, not the square.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

/-- Is the parent edge of `x` generation-live, and where does it go? -/
def liveParent (τ : MachineState) (x : DomainId × Slot) :
    Option (DomainId × Slot) := do
  let p ← τ.parentOf x.1 x.2
  if p.gen = (τ.doms p.dom).slotGen p.slot then pure (p.dom, p.slot)
  else none

/-- A live parent chain of length `< n` from `x` ends in an edge pointing
at `root` (the mark semantics of `rv_r` after `log₂ n` rounds; matches
`Kernel.markStep` unfolded along one chain). -/
def reachRootN (τ : MachineState) (root : CapRef) :
    Nat → DomainId × Slot → Bool
  | 0, _ => false
  | n + 1, x =>
      match τ.parentOf x.1 x.2 with
      | some p =>
          p = root ||
          (decide (p.gen = (τ.doms p.dom).slotGen p.slot)
            && reachRootN τ root n (p.dom, p.slot))
      | none => false

/-- The `n`-step parent chain from `x` exists with every edge
generation-live (the semantics of `rv_v`). -/
def liveChainN (τ : MachineState) : Nat → DomainId × Slot → Bool
  | 0, _ => true
  | n + 1, x =>
      match liveParent τ x with
      | some y => liveChainN τ n y
      | none => false

/-- The endpoint of the `n`-step live parent chain (meaningful only where
`liveChainN` holds; the semantics of `rv_j`). -/
def chainEndN (τ : MachineState) : Nat → DomainId × Slot → DomainId × Slot
  | 0, x => x
  | n + 1, x =>
      match liveParent τ x with
      | some y => chainEndN τ n y
      | none => x

/-- The revoked root: the in-flight word's issuing domain and the handle
fields of its `rs1` register (what `rvInit`'s `rootEnc` samples). -/
def rvRoot (σ : Loom.Hw.St) : CapRef :=
  let e : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2)
  let hw := ((Hw.abs σ).doms e).reg
    (operandsOf (σ.regs "if_word" 32)).rs1
  { dom := e
    slot := finOfBv (by decide) (hw.extractLsb' 0 4)
    gen := hw.extractLsb' 4 8 }

/-- The doubling rounds completed at pre-cycle countdown value `cl`. -/
def rvRounds (cl : Nat) : Nat := revokeCost - 1 - cl

/-- **The rv-coupling invariant** (statement; preservation is the tier-4
obligation). With an in-flight `cap_revoke` past its first countdown
cycle, the hidden mark-engine vectors are `2^k`-round descendant marking
from the revoked root on the abstraction. -/
def RvSync (σ : Loom.Hw.St) : Prop :=
  σ.regs "if_v" 1 = 1#1 →
  (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6 →
  (σ.regs "if_cl" 8).toNat < revokeCost →
  ∀ (c : DomainId) (s : Slot),
    (σ.regs (Hw.rvR (Hw.nodeOf c s)) 1
      = if reachRootN (Hw.abs σ) (rvRoot σ)
            (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s)
        then 1#1 else 0#1)
    ∧ (σ.regs (Hw.rvV (Hw.nodeOf c s)) 1
      = if liveChainN (Hw.abs σ)
            (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s)
        then 1#1 else 0#1)
    ∧ (liveChainN (Hw.abs σ)
        (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s) = true →
      σ.regs (Hw.rvJ (Hw.nodeOf c s)) 6
        = BitVec.ofNat 6 (Hw.nodeOf
            (chainEndN (Hw.abs σ)
              (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s)).1
            (chainEndN (Hw.abs σ)
              (2 ^ rvRounds (σ.regs "if_cl" 8).toNat) (c, s)).2).val)

/- Deferred obligations (tier 4, NEXTSTEPS §1.6):

1. `rvInit` establishes `RvSync` at `k = 0` (chains of length < 1:
   exactly the direct parent-is-root test `rvInit` computes; `2^0`-step
   chain = one live edge; `rv_j` = the parent's node index).
2. `rvStep` doubles: `reachRootN (2^k) ∨ (liveChainN (2^k) ∧
   reachRootN (2^k) at chainEndN (2^k)) = reachRootN (2^(k+1))`, and
   likewise for `liveChainN`/`chainEndN` composition.
3. Frame preservation by refill/mover/tick and vacuity at issue/retire.
4. `marks_eq_reachRootN`: `Kernel.marks root d s = reachRootN root
   (numDomains * numSlots) (d, s)` (induction on the `markStep` fold),
   plus saturation `n ≥ numDomains * numSlots → reachRootN n =
   reachRootN (numDomains * numSlots)` (pigeonhole on acyclic parent
   chains — `AcyclicInv` supplies acyclicity through the arm's `hsr`).
5. The retirement arm then reads `revKilled = marksAt` = the fixpoint.
-/

end Machines.Lnp64u.Theorems.RMC
