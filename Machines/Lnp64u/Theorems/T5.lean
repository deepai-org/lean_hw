import Machines.Lnp64u.Logic.Wf
import Mathlib.Data.List.Basic

/-!
# T5 — Noninterference (architectural, path-free pairs)

Donation deliberately couples timing along authority paths, so the theorem
quantifies over pairs with *no* path, and observes architectural state
modulo stuttering: an isolated domain's destuttered trajectory is a
function of its own configuration and code only. Stated as a two-manifest
(2-safety) property; Phase 1 discharges instances via the L2 engines, the
general statement by unwinding.
-/

namespace Machines.Lnp64u.Theorems.T5

open Machines.Lnp64u Loom

/-- Domain `d` is authority-isolated in manifest `m`: it holds no gate
capabilities, serves no gate, and its root memory ranges overlap no other
domain's. Path-freedom, syntactically. -/
def Isolated (m : Manifest) (d : DomainId) : Prop :=
  (∀ s g, (m.doms d).initCaps s ≠ some (.gate g)) ∧
  (∀ g, (m.gates g).callee ≠ d) ∧
  (∀ d' s s' b l p b' l' p', d' ≠ d →
    (m.doms d).initCaps s = some (.mem b l p) →
    (m.doms d').initCaps s' = some (.mem b' l' p') →
    b.toNat + l.toNat ≤ b'.toNat ∨ b'.toNat + l'.toNat ≤ b.toNat)

/-- Two manifests agree on everything `d` can see: `d`'s configuration and
the ROM under `d`'s root ranges. -/
def AgreeOn (m₁ m₂ : Manifest) (d : DomainId) : Prop :=
  m₁.doms d = m₂.doms d ∧
  (∀ (s : Slot) (b : Addr) (l : BitVec 13) (p : Perms) (a : Addr),
    (m₁.doms d).initCaps s = some (.mem b l p) →
    b.toNat ≤ a.toNat → a.toNat < b.toNat + l.toNat →
    m₁.rom a = m₂.rom a)

/-- Remove consecutive duplicates. -/
def destutter : List DomainState → List DomainState
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if x.regs = y.regs ∧ x.pc = y.pc ∧ x.run = y.run ∧ x.cause = y.cause
      then destutter (y :: rest) else x :: destutter (y :: rest)

/-- `d`'s architectural trajectory over `n` cycles. -/
def trajectory (m : Manifest) (d : DomainId) (n : Nat) : List DomainState :=
  (List.range n).map fun i => (stepN m i m.initState).doms d

/-- **T5.** An isolated domain's destuttered trajectory is independent of
everything outside its own configuration and code: under agreement, one
machine's destuttered trajectory is a prefix of the other's (run long
enough). -/
theorem noninterference (m₁ m₂ : Manifest) (h₁ : m₁.WF) (h₂ : m₂.WF)
    (d : DomainId) (hiso₁ : Isolated m₁ d) (hiso₂ : Isolated m₂ d)
    (hag : AgreeOn m₁ m₂ d) :
    ∀ n, ∃ k, (destutter (trajectory m₁ d n)) <+: (destutter (trajectory m₂ d k)) := by
  sorry

end Machines.Lnp64u.Theorems.T5
