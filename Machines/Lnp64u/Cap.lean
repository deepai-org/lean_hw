-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Types

/-!
# Capabilities: handle bit-shape, entries, lineage (L0)

The full-LNP64 handle shape at µ widths (Rule 3: µ is a morphism, not a
mascot). Three design decisions are recorded here:

1. **Handles are (slot, generation, class) triples packed in a word.** A
   handle is valid iff its generation equals the slot's current generation
   and an entry is present. Generation `0` is null: `encode` of any handle
   with generation ≥ 1 is provably nonzero (T1 null-handle
   unconstructibility).

2. **The parent pointer lives in exactly one place: the lineage cell.**
   A derived capability's entry points (via `lineage`) into its owner's
   lineage table; the cell holds the parent `CapRef`. Root (manifest)
   capabilities have no cell. Allocation of a cell can fail — that is the
   per-domain lineage quota, and T9 counts occupied cells.

3. **Generations retire by saturation.** A slot's generation starts at 1,
   is bumped on every free, and saturates at `genRetired = 255`, after which
   the slot is permanently unusable. No generation is ever reused, which is
   the no-resurrection half of T3.
-/

namespace Machines.Lnp64u

/-- Capability classes. µ has exactly two. -/
inductive CapClass where
  | mem
  | gate
deriving Repr, DecidableEq

/-- Memory permissions. `mem_grant` and `map` enforce W^X (T8): no
capability or region ever carries both `w` and `x`. -/
structure Perms where
  r : Bool
  w : Bool
  x : Bool
deriving Repr, DecidableEq

namespace Perms

/-- `p ≤ q`: every permission in `p` is also in `q` (narrowing order). -/
def le (p q : Perms) : Bool :=
  (!p.r || q.r) && (!p.w || q.w) && (!p.x || q.x)

/-- The W^X predicate. -/
def wx (p : Perms) : Bool := !(p.w && p.x)

end Perms

/-- A machine-wide reference to a capability *at a specific generation*:
the identity that lineage cells, region registers, and the Mover hold, and
that revoke retires. -/
structure CapRef where
  dom  : DomainId
  slot : Slot
  gen  : Gen
deriving Repr, DecidableEq

/-! ## Handles: the register-value view of a capability -/

/-- A handle as held in a register: names a slot in the *holding* domain's
own cap table. The bit-shape (LSB-first): slot `[3:0]`, generation `[11:4]`,
class `[12]`, bits `[31:13]` zero. -/
structure Handle where
  slot  : Slot
  gen   : Gen
  cls   : CapClass
deriving Repr, DecidableEq

namespace Handle

/-- Pack a handle into its architectural word. -/
def encode (h : Handle) : Loom.Word32 :=
  (BitVec.ofNat 32 h.slot.val) |||
  ((h.gen.setWidth 32) <<< 4) |||
  (((if h.cls = .gate then 1#1 else 0#1).setWidth 32) <<< 12)

/-- Decode a word as a handle. Total: reserved bits are ignored on read
(the *write* side never produces them; T1 checks round-trip on encode). -/
def decode (w : Loom.Word32) : Handle where
  slot := ⟨(w.extractLsb' 0 4).toNat, by
    have := (w.extractLsb' 0 4).isLt; simpa [numSlots] using this⟩
  gen  := w.extractLsb' 4 8
  cls  := if w.getLsbD 12 then .gate else .mem

/-- The null handle: the all-zero word, generation 0. -/
def null : Loom.Word32 := 0

end Handle

/-! ## Capability-table entries and lineage cells -/

/-- The class-specific payload of a capability. Memory ranges are word
ranges `[base, base + len)` in physical memory; `len` is 13 bits so the
whole 4096-word memory is expressible. -/
inductive CapKind where
  /-- Authority over the word range `[base, base + len)` with `perms`. -/
  | mem (base : Addr) (len : BitVec 13) (perms : Perms)
  /-- Authority to call gate `g`. -/
  | gate (g : GateId)
deriving Repr, DecidableEq

namespace CapKind

/-- Class of a kind. -/
def cls : CapKind → CapClass
  | .mem .. => .mem
  | .gate _ => .gate

/-- Does a memory kind cover word address `a` with permission check `need`?
Gate kinds cover nothing. -/
def covers (k : CapKind) (a : Addr) (need : Perms) : Bool :=
  match k with
  | .mem base len perms =>
      decide (base.toNat ≤ a.toNat) &&
      decide (a.toNat < base.toNat + len.toNat) &&
      need.le perms
  | .gate _ => false

end CapKind

/-- One occupied capability slot. `lineage = none` iff this is a root
(manifest) capability; otherwise it indexes the owner's lineage table. -/
structure CapEntry where
  kind    : CapKind
  lineage : Option LineageId
deriving Repr, DecidableEq

/-- A lineage cell: the single home of the parent pointer (design decision
2 above). Occupied cells are the T9-conserved lineage resource. -/
structure LineageCell where
  parent : CapRef
deriving Repr, DecidableEq

/-- The retired generation: a slot whose generation has saturated here is
permanently dead. -/
def genRetired : Gen := 255

/-- The generation stamped on manifest capabilities and fresh slots. -/
def genFirst : Gen := 1

/-! ## Region registers: cached memory authority -/

/-- A region register: a cached, swept copy of a memory capability's
authority. `backing` names the capability (at its generation) whose
authority this caches — the sweep in `cap_revoke` clears every region whose
backing was retired (T3's core mechanism). -/
structure Region where
  base    : Addr
  len     : BitVec 13
  perms   : Perms
  backing : CapRef
deriving Repr, DecidableEq

namespace Region

/-- Does this region authorize access to word `a` with permissions `need`? -/
def covers (rg : Region) (a : Addr) (need : Perms) : Bool :=
  decide (rg.base.toNat ≤ a.toNat) &&
  decide (a.toNat < rg.base.toNat + rg.len.toNat) &&
  need.le rg.perms

end Region

end Machines.Lnp64u
