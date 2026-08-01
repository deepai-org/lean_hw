-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Core.Ts
import Machines.Epoch.Protocol
import Mathlib

/-!
# The LNP64 capability handle model, mechanized (Layer 1)

Normative source: `lnp64_isa.md` §2.2 ("How a capability is unforgeable — the
handle model, not tagged memory") and Appendix F, mandatory protocol machine 2
("Capability table walk + fill … the fill path is a page-walker-class
sequencer"; "Capability transfer — the install-time transaction: snapshot,
rights derivation, re-key, transfer-class commit"). Appendix F makes the
mechanized protocol spec *the* behavioral definition; this file is the
candidate normative artifact for that machine's use/fill half, and
`Machines/CapWalk/CAPWALK_SPEC.md` is the binding scope/obligation document
it discharges.

## What is modelled

§2.2 fixes the encoding: a handle is a `u64` with `bit63 = 0`,
`slot = bits[62:39]`, `epoch = bits[38:0]`, and **epoch `0` is
architecturally reserved-invalid**. The §"Handle encoding" section below is
that layout, and `T_C1_null_unconstructible` is §2.2's own claim that the
null handle is "an encoding theorem, not a convention".

§2.2 also fixes that **both invalidation mechanisms are the same primitive**:
"the slot's embedded cell (reuse safety) and the shared lineage cell
(revocation) are epoch cells, §3". So this file does not restate freshness:
its cells *are* `Machines.Epoch.Protocol.Cell`, the lineage check *is*
`Machines.Epoch.Protocol.useLocal`, and `T_C4` (revocation reaches every
descendant) is discharged by transporting the lineage cells into
`Machines.Epoch.Protocol.sys` and applying §3's `T_E1_never_ok`.

The check order is §2.2's, verbatim — "slot occupied, handle epoch ==
slot-cell epoch, lineage-cell epoch current, required rights present,
range/class valid. **Checks occur in that order.**" — with §2.2's total
condition mapping, including the subtle case that an *empty* slot whose
current embedded epoch nevertheless matches is `-BADREF`, not `-STALE`.

Everything here is a kernel proof: no `sorry`, no `native_decide`, no new
axioms. Deviations from `CAPWALK_SPEC.md` are recorded there under
§"Deviations"; nothing is silently narrowed.
-/

namespace Machines.CapWalk.Protocol

open Loom
open Machines.Epoch.Protocol (Cell Policy maxE satInc)

/-! ## §2.2 vocabulary -/

/-- The four architected outcomes of a capability use. §2.2's condition
mapping names three failures (`-BADREF`, `-STALE`, `-DENIED`) plus success.
There is no `-POISONED` here: poison is a §3 bump *policy*, and v1's
invalidations are `lazy` (see `CAPWALK_SPEC.md` §Deviations, C6). -/
inductive Outcome where
  | ok
  | badref
  | stale
  | denied
  deriving DecidableEq, Repr, Inhabited

/-- §2.2's slot lifetime class, applied by `dreplace.commit` (§11.5). Carried
on the entry; v1 does not act on it (`CAPWALK_SPEC.md` §Scope stages
`dreplace.commit` out). -/
inductive Lifetime where
  | persist
  | dropOnStateReplacement
  deriving DecidableEq, Repr, Inhabited

/-- A rights mask. §2.2 puts rights on the *entry*, never on the handle. -/
abbrev Rights := BitVec 8

/-- Rights containment: `a` is no wider than `b`. This is the order
`cap_dup`'s "monotonically narrowed rights" is monotone in. -/
def rightsSub (a b : Rights) : Bool := (a &&& b) == a

@[simp] theorem rightsSub_refl (a : Rights) : rightsSub a a = true := by
  simp [rightsSub]

/-- The range check: the requested `[off, off+len)` lies inside the entry's
`[base, base+blen)`. -/
def rangeIn (off len base blen : Nat) : Bool :=
  decide (base ≤ off) && decide (off + len ≤ base + blen)

@[simp] theorem rangeIn_self (base blen : Nat) : rangeIn base blen base blen = true := by
  simp [rangeIn]

/-! ## Handle encoding (§2.2, fixed widths)

"a `u64` with a fixed layout: **bit 63 = 0** …, **bits `[62:39]` = 24-bit slot
index** …, **bits `[38:0]` = the 39-bit epoch the slot's embedded cell must
currently hold**". These widths are architectural constants, so this section
is stated at exactly 64/24/39. -/

/-- §2.2's epoch field width. -/
abbrev epochBits : Nat := 39
/-- §2.2's slot-index field width. -/
abbrev slotBits : Nat := 24

/-- A capability handle: an ordinary `u64`. -/
abbrev Handle := BitVec 64

/-- The handle's epoch field, `bits[38:0]`. -/
def hEpoch (h : Handle) : BitVec epochBits := BitVec.extractLsb' 0 epochBits h

/-- The handle's slot field, `bits[62:39]`. -/
def hSlot (h : Handle) : BitVec slotBits := BitVec.extractLsb' epochBits slotBits h

/-- The handle's sign bit, which §2.2 pins to `0` "so a handle is always
non-negative and never collides with a `-CONDITION` return". -/
def hSign (h : Handle) : Bool := h.getLsbD 63

/-- Assemble a handle: `slot << 39 | epoch`. -/
def mkHandle (sl : BitVec slotBits) (e : BitVec epochBits) : Handle :=
  ((BitVec.setWidth 64 sl) <<< epochBits) ||| (BitVec.setWidth 64 e)

/-- §2.2's *live handle* predicate: sign bit clear and epoch not the reserved
`0`. "a live handle is `slot << 39 | epoch` with `epoch >= 1`". -/
def Live (h : Handle) : Prop := hSign h = false ∧ hEpoch h ≠ 0#epochBits

/-! ## Entries and state

§2.2: "The authority lives in the table entry, in hardware-owned protected
storage no instruction can write directly. Entry fields: class, rights,
range, the slot's embedded epoch cell, a shared epoch-cell reference (the
lineage), and the slot lifetime class …; `SEALED` …; and reserved bits". -/

/-- The spillable part of a capability-table entry: everything except the
slot's embedded epoch cell, which stays on-chip at the checking interface
(`EPOCH_SPEC.md` §"Design decision", rule 1). `parent` is the engine-owned
derivation record: the `{slot, epoch}` of the authorizing capability
`cap_dup` minted this entry from (§2.2: "New entries are minted only by the
engine, only from an authorizing capability you already hold"). -/
structure EntryData (W N L : Nat) where
  /-- §2.2's object/interface class. -/
  cls : Nat
  /-- §2.2's rights field. -/
  rights : Rights
  /-- Range base. -/
  base : Nat
  /-- Range length. -/
  len : Nat
  /-- The shared epoch-cell reference: §2.2's lineage. -/
  lineage : Fin L
  /-- The lineage epoch this entry was stamped with — §2.2's "shared
  lineage/stamp epoch". -/
  linStamp : BitVec W
  /-- §16.3's `SEALED` bit (carried, not acted on in v1). -/
  sealed : Bool
  /-- §11.5's slot lifetime class (carried, not acted on in v1). -/
  lifetime : Lifetime
  /-- The authorizing `{slot, epoch}` this entry was derived from. -/
  parent : Option (Fin N × BitVec W)
  deriving DecidableEq

/-- The narrowing order on entries: `a` is a `cap_dup` of `b` only if it is
narrower in rights and range, of the same class, and **on the same lineage
cell with the same stamp** — which is what makes one `cap_revoke` reach every
descendant (§2.2: "all descendants sharing one cell"). -/
def Narrows {W N L : Nat} (a b : EntryData W N L) : Bool :=
  rightsSub a.rights b.rights && (a.cls == b.cls) &&
    decide (b.base ≤ a.base) && decide (a.base + a.len ≤ b.base + b.len) &&
    (a.lineage == b.lineage) && (a.linStamp == b.linStamp)

/-- Protocol state for one domain's capability table: `N` slots.

* `cell i` — the slot's **embedded** §3 epoch cell (its `occupied` bit is
  §2.2's "slot occupied");
* `ent i` — the abstract entry map (`EPOCH_SPEC.md` §SUPERSEDING DOCTRINE
  point 3: "engine specs are stated against an abstract machine whose table
  is one mathematical map");
* `backing i` — the spilled copy in the backing store, which the
  page-walker-class fill path reads;
* `resident i` — is the slot in the hot on-chip cache;
* `lin l` — the `L` **shared lineage** §3 epoch cells. -/
structure St (W N L : Nat) where
  /-- The per-slot embedded epoch cells (hardware-owned, on-chip). -/
  cell : Fin N → Cell W
  /-- The abstract per-slot entries. -/
  ent : Fin N → EntryData W N L
  /-- The backing-store copy of each entry. -/
  backing : Fin N → EntryData W N L
  /-- Residency in the hot cache. -/
  resident : Fin N → Bool
  /-- The shared lineage cells. -/
  lin : Fin L → Cell W

/-- A presented use: the decoded handle plus what the operation demands.
`wellFormed` is §2.2's structural predicate — sign bit clear, epoch not the
reserved `0`, slot index in range (see `decode`). -/
structure Query (W : Nat) where
  /-- The raw slot index carried by the handle. -/
  slotIx : Nat
  /-- The handle's epoch field — §2.2's "check value, not a grant". -/
  epoch : BitVec W
  /-- Handle shape validates. -/
  wellFormed : Bool
  /-- The rights this operation requires. -/
  need : Rights
  /-- The object/interface class this operation requires. -/
  cls : Nat
  /-- Requested range offset. -/
  off : Nat
  /-- Requested range length. -/
  len : Nat
  deriving DecidableEq

/-- Decode a `u64` into a query at §2.2's fixed widths. `wellFormed`
transcribes exactly the three structural facts §2.2 lists: bit 63 clear,
epoch ≠ 0 (the reserved-invalid value), and an in-range slot index. -/
def decode (N : Nat) (h : Handle) (need : Rights) (cls off len : Nat) :
    Query epochBits where
  slotIx := (hSlot h).toNat
  epoch := hEpoch h
  wellFormed := (hSign h == false) && (hEpoch h != 0#epochBits) &&
    decide ((hSlot h).toNat < N)
  need := need
  cls := cls
  off := off
  len := len

/-! ## §2.2's check, in §2.2's order

"On every *use* the engine checks: slot occupied, **handle epoch == slot-cell
epoch**, lineage-cell epoch current, required rights present, range/class
valid. … **Checks occur in that order. No section or operation may choose a
different condition for the same predicate.**"

Condition mapping (total and universal): null-where-not-admitted /
out-of-range or malformed slot index / **an empty slot whose current embedded
epoch nevertheless matches** / a live entry of the wrong class → `-BADREF`;
any embedded slot-epoch mismatch or shared lineage/stamp mismatch →
`-STALE`; a valid live reference lacking required rights or range →
`-DENIED`. -/

/-- The lineage check, presented to §3's own checker. §2.2: the lineage cell
*is* a §3 epoch cell, so this is `Machines.Epoch.Protocol.useLocal` applied
to it, not a restatement. A lineage cell is always occupied and never
class-or-rights qualified, so the only outcomes it can produce are §3's
`ok`/`stale` (`-POISONED` needs a poison bump, which v1 does not issue). -/
def linReq {W N L : Nat} (ed : EntryData W N L) :
    Machines.Epoch.Protocol.Req W where
  cellIx := ed.lineage.val
  epoch := ed.linStamp
  wellFormed := true
  classOk := true
  rights := true

/-- §3's verdict on the shared lineage cell, read locally. -/
def linOutcome {W N L : Nat} (lc : Cell W) (ed : EntryData W N L) :
    Machines.Epoch.Protocol.Outcome :=
  Machines.Epoch.Protocol.useLocal lc lc.epoch (linReq ed)

/-- The ordered outcome function on already-derived scalars. This is the
priority spine; `check` below feeds it the entry-derived values. -/
def outcome {W : Nat} (occ dead : Bool) (cep qep : BitVec W)
    (wf linFail rightsOk clsOk rangeOk : Bool) : Outcome :=
  -- structural: malformed handle / out-of-range or null-where-not-admitted
  if wf = false then .badref
  -- 1. slot occupied  (empty + matching embedded epoch is BADREF, not STALE)
  else if occ = false then (if cep = qep then .badref else .stale)
  -- 2. handle epoch == slot-cell epoch  (saturated death is a freshness failure)
  else if cep ≠ qep then .stale
  else if dead = true then .stale
  -- 3. lineage-cell epoch current
  else if linFail = true then .stale
  -- 4. required rights present
  else if rightsOk = false then .denied
  -- 5. range/class valid
  else if clsOk = false then .badref
  else if rangeOk = false then .denied
  else .ok

/-- §2.2's use-check against one slot: the embedded cell `c`, the shared
lineage cell `lc` the entry names, the entry, and the query. Total. -/
def check {W N L : Nat} (c lc : Cell W) (ed : EntryData W N L) (q : Query W) :
    Outcome :=
  outcome c.occupied c.dead c.epoch q.epoch q.wellFormed
    (linOutcome lc ed != Machines.Epoch.Protocol.Outcome.ok)
    (rightsSub q.need ed.rights) (ed.cls == q.cls)
    (rangeIn q.off q.len ed.base ed.len)

/-- The state-level use. An out-of-range slot index is structural `-BADREF`
(§2.2's "an out-of-range/malformed slot index → `-BADREF`"). -/
def use {W N L : Nat} (s : St W N L) (q : Query W) : Outcome :=
  if h : q.slotIx < N then
    check (s.cell ⟨q.slotIx, h⟩) (s.lin (s.ent ⟨q.slotIx, h⟩).lineage)
      (s.ent ⟨q.slotIx, h⟩) q
  else .badref

/-- The self-query an entry presents about itself: the authorizing check
`cap_dup` performs on the capability you already hold. -/
def selfQuery {W N L : Nat} (c : Cell W) (ed : EntryData W N L) : Query W where
  slotIx := 0
  epoch := c.epoch
  wellFormed := true
  need := ed.rights
  cls := ed.cls
  off := ed.base
  len := ed.len

/-! ## Cell transitions borrowed from §3

Both invalidation mechanisms are §3 bumps; only the occupancy bit is
capability-layer. -/

/-- Dropping a slot: §2.2's "Dropping a slot bumps its embedded cell", and
the slot becomes empty. -/
def Cell.dropped {W : Nat} (c : Cell W) : Cell W :=
  { c.bumped Policy.lazy with occupied := false }

/-- Minting into an empty slot: a fresh incarnation, so the embedded cell is
bumped and the slot becomes occupied. This is what makes "a stale handle to a
recycled slot fails forever" (§2.2) true across reuse. -/
def Cell.minted {W : Nat} (c : Cell W) : Cell W :=
  { c.bumped Policy.lazy with occupied := true }

@[simp] theorem Cell.dropped_epoch {W : Nat} (c : Cell W) :
    (Cell.dropped c).epoch = satInc c.epoch := rfl
@[simp] theorem Cell.dropped_occupied {W : Nat} (c : Cell W) :
    (Cell.dropped c).occupied = false := rfl
@[simp] theorem Cell.dropped_dead {W : Nat} (c : Cell W) :
    (Cell.dropped c).dead = (c.dead || decide (satInc c.epoch = maxE W)) := rfl
@[simp] theorem Cell.minted_epoch {W : Nat} (c : Cell W) :
    (Cell.minted c).epoch = satInc c.epoch := rfl
@[simp] theorem Cell.minted_occupied {W : Nat} (c : Cell W) :
    (Cell.minted c).occupied = true := rfl
@[simp] theorem Cell.minted_dead {W : Nat} (c : Cell W) :
    (Cell.minted c).dead = (c.dead || decide (satInc c.epoch = maxE W)) := rfl

/-! ## Transitions -/

/-- `cap_dup`'s guard: an authorizing capability that passes its own check,
an empty and not-retired destination slot, monotone narrowing, and the
derivation record naming the authorizer's current `{slot, epoch}`. -/
def dupOk {W N L : Nat} (s : St W N L) (src dst : Fin N)
    (ed : EntryData W N L) : Bool :=
  (check (s.cell src) (s.lin (s.ent src).lineage) (s.ent src)
      (selfQuery (s.cell src) (s.ent src)) == Outcome.ok) &&
    ((s.cell dst).occupied == false) && ((s.cell dst).dead == false) &&
    Narrows ed (s.ent src) &&
    (ed.parent == some (src, (s.cell src).epoch))

/-- The protocol's transition alphabet. `use` is an observation (§3/D7): the
check is a pure read, modelled as an enabled stutter step so that a run can
interleave uses with invalidations. -/
inductive Ev (W N L : Nat) where
  /-- A capability use (pure observation). -/
  | use (q : Query W)
  /-- Cold fill: the page-walker-class sequencer installs slot `i` from the
  backing store. -/
  | fill (i : Fin N)
  /-- Write-back eviction of slot `i`. -/
  | evict (i : Fin N)
  /-- Drop slot `i`: bump its embedded cell (§2.2 reuse safety). -/
  | drop (i : Fin N)
  /-- `cap_revoke`: bump the shared lineage cell `l` once, O(1). -/
  | revoke (l : Fin L)
  /-- `cap_dup src dst ed`: mint `ed` into the empty slot `dst` from the
  authorizing capability in `src`, with monotonically narrowed rights. -/
  | dup (src dst : Fin N) (ed : EntryData W N L)

/-- The transition function; `none` = the event is disabled. -/
def stepEv {W N L : Nat} (s : St W N L) : Ev W N L → Option (St W N L)
  | .use _ => some s
  | .fill i =>
      if s.resident i = true then none
      else some { s with
        ent := Function.update s.ent i (s.backing i)
        resident := Function.update s.resident i true }
  | .evict i =>
      if s.resident i = false then none
      else some { s with
        backing := Function.update s.backing i (s.ent i)
        resident := Function.update s.resident i false }
  | .drop i =>
      if (s.cell i).occupied = false then none
      else some { s with cell := Function.update s.cell i (Cell.dropped (s.cell i)) }
  | .revoke l =>
      some { s with lin := Function.update s.lin l ((s.lin l).bumped Policy.lazy) }
  | .dup src dst ed =>
      if dupOk s src dst ed then
        some { s with
          cell := Function.update s.cell dst (Cell.minted (s.cell dst))
          ent := Function.update s.ent dst ed
          backing := Function.update s.backing dst ed }
      else none

/-- The step relation. -/
def Step {W N L : Nat} (s s' : St W N L) : Prop := ∃ e, stepEv s e = some s'

/-- Reset states: every embedded and lineage cell is a fresh §3 cell (epoch
`≥ 1`, `dead` exactly at saturation, unpoisoned), every lineage cell is
occupied, the backing store agrees with the table, and no entry claims a
derivation (root capabilities are engine-installed, not `cap_dup`ed). -/
structure Init {W N L : Nat} (s : St W N L) : Prop where
  /-- §2.2: epoch `0` is reserved-invalid; every slot's first live epoch is 1. -/
  cellNonzero : ∀ i, (s.cell i).epoch ≠ 0#W
  /-- `dead` is exactly saturation. -/
  cellDeadIffMax : ∀ i, (s.cell i).dead = decide ((s.cell i).epoch = maxE W)
  /-- Lineage cells obey the same reserved-invalid rule. -/
  linNonzero : ∀ l, (s.lin l).epoch ≠ 0#W
  /-- Lineage cells: `dead` exactly at saturation. -/
  linDeadIffMax : ∀ l, (s.lin l).dead = decide ((s.lin l).epoch = maxE W)
  /-- A lineage cell always exists. -/
  linOccupied : ∀ l, (s.lin l).occupied = true
  /-- v1 issues only `lazy` bumps. -/
  linClean : ∀ l, (s.lin l).poison = false
  /-- The backing store starts faithful. -/
  fidelity : ∀ i, s.backing i = s.ent i
  /-- No reset entry claims an authorizer. -/
  rootless : ∀ i, (s.ent i).parent = none

/-- The capability protocol as a `Loom.TSys`. -/
def sys (W N L : Nat) : Loom.TSys where
  S := St W N L
  init := Init
  step := Step

/-- Multi-step reachability from a given state — the "forever" of §2.2's
guarantees. -/
abbrev Run {W N L : Nat} (s t : St W N L) : Prop :=
  Relation.ReflTransGen (@Step W N L) s t

/-! ## Small §3 arithmetic facts used here (not restated: derived) -/

theorem satInc_ne_zero {W : Nat} {e : BitVec W} (h : e ≠ 0#W) : satInc e ≠ 0#W := by
  by_cases hm : e = maxE W
  · rw [Machines.Epoch.Protocol.satInc_eq_of_max hm]; exact h
  · intro hz
    have h1 := Machines.Epoch.Protocol.toNat_satInc_of_ne hm
    rw [hz] at h1
    exact absurd h1 (by simp)

theorem bumped_deadIffMax {W : Nat} {c : Cell W} {p : Policy}
    (h : c.dead = decide (c.epoch = maxE W)) :
    (c.bumped p).dead = decide ((c.bumped p).epoch = maxE W) := by
  rw [Machines.Epoch.Protocol.Cell.bumped_dead, Machines.Epoch.Protocol.Cell.bumped_epoch]
  by_cases hd : c.dead = true
  · rw [hd, Bool.true_or]
    rw [hd] at h
    have : c.epoch = maxE W := of_decide_eq_true h.symm
    rw [Machines.Epoch.Protocol.satInc_eq_of_max this, this]
    simp
  · simp only [Bool.not_eq_true] at hd
    rw [hd, Bool.false_or]

/-- Strict increase: a live (non-saturated) cell's bump moves the epoch. -/
theorem satInc_strict {W : Nat} {c : Cell W}
    (hdm : c.dead = decide (c.epoch = maxE W)) (hd : c.dead = false) :
    (c.epoch).toNat < (satInc c.epoch).toNat := by
  rw [hd] at hdm
  have hne : c.epoch ≠ maxE W := by
    intro he; rw [he] at hdm; simp at hdm
  rw [Machines.Epoch.Protocol.toNat_satInc_of_ne hne]
  omega

/-- A saturated cell's bump is a no-op on the epoch. -/
theorem satInc_of_dead {W : Nat} {c : Cell W}
    (hdm : c.dead = decide (c.epoch = maxE W)) (hd : c.dead = true) :
    satInc c.epoch = c.epoch := by
  rw [hd] at hdm
  exact Machines.Epoch.Protocol.satInc_eq_of_max (of_decide_eq_true hdm.symm)

/-! ## Facts about the check -/

/-- Everything `ok` implies, in one lemma. -/
theorem outcome_ok_iff {W : Nat} {occ dead : Bool} {cep qep : BitVec W}
    {wf linFail rightsOk clsOk rangeOk : Bool} :
    outcome occ dead cep qep wf linFail rightsOk clsOk rangeOk = .ok ↔
      (wf = true ∧ occ = true ∧ cep = qep ∧ dead = false ∧ linFail = false ∧
        rightsOk = true ∧ clsOk = true ∧ rangeOk = true) := by
  constructor
  · intro h
    unfold outcome at h
    split at h; · exact absurd h (by simp)
    split at h; · split at h <;> exact absurd h (by simp)
    split at h; · exact absurd h (by simp)
    split at h; · exact absurd h (by simp)
    split at h; · exact absurd h (by simp)
    split at h; · exact absurd h (by simp)
    split at h; · exact absurd h (by simp)
    split at h; · exact absurd h (by simp)
    rename_i h1 h2 h3 h4 h5 h6 h7 h8
    simp only [Bool.not_eq_false, Bool.not_eq_true, ne_eq, not_not] at *
    refine ⟨by simpa using h1, by simpa using h2, by simpa using h3,
      by simpa using h4, by simpa using h5, by simpa using h6,
      by simpa using h7, by simpa using h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    simp [outcome, h1, h2, h3, h4, h5, h6, h7, h8]

theorem check_ok_iff {W N L : Nat} {c lc : Cell W} {ed : EntryData W N L}
    {q : Query W} :
    check c lc ed q = .ok ↔
      (q.wellFormed = true ∧ c.occupied = true ∧ c.epoch = q.epoch ∧
        c.dead = false ∧ linOutcome lc ed = Machines.Epoch.Protocol.Outcome.ok ∧
        rightsSub q.need ed.rights = true ∧ (ed.cls == q.cls) = true ∧
        rangeIn q.off q.len ed.base ed.len = true) := by
  rw [check, outcome_ok_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, by simpa using h5, h6, h7, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, by simp [h5], h6, h7, h8⟩

/-- The failure side, in the form the "forever" theorems consume: a stale or
saturated embedded cell can never be `ok`. -/
theorem check_ne_ok_of_freshness {W N L : Nat} {c lc : Cell W}
    {ed : EntryData W N L} {q : Query W}
    (h : c.epoch ≠ q.epoch ∨ c.dead = true) : check c lc ed q ≠ .ok := by
  intro hok
  obtain ⟨_, _, he, hd, _, _, _, _⟩ := check_ok_iff.mp hok
  rcases h with h | h
  · exact h he
  · rw [hd] at h; exact absurd h (by simp)

theorem check_ne_ok_of_lineage {W N L : Nat} {c lc : Cell W}
    {ed : EntryData W N L} {q : Query W}
    (h : linOutcome lc ed ≠ Machines.Epoch.Protocol.Outcome.ok) :
    check c lc ed q ≠ .ok := by
  intro hok
  exact h (check_ok_iff.mp hok).2.2.2.2.1

/-! ## The inductive invariant -/

/-- The protocol invariant.

* the freshness fields of every §3 cell are well-formed (`§3`'s reserved-zero
  and saturation rules, needed to make bumps strict);
* `fidelity` — the backing store agrees with the abstract table. This is the
  **hook the authenticated store discharges** (T-C6); v1 has no corruption
  event, and `CAPWALK_SPEC.md` §Deviations records that;
* `parentLe`/`noAmp` — the derivation record never names a *future*
  incarnation of its authorizer, and while it names the *current* one, the
  derived entry is narrower. Together these are T-C3. -/
structure Inv {W N L : Nat} (s : St W N L) : Prop where
  /-- Epoch `0` is reserved-invalid for embedded cells. -/
  cellNonzero : ∀ i, (s.cell i).epoch ≠ 0#W
  /-- `dead` is exactly saturation for embedded cells. -/
  cellDeadIffMax : ∀ i, (s.cell i).dead = decide ((s.cell i).epoch = maxE W)
  /-- Epoch `0` is reserved-invalid for lineage cells. -/
  linNonzero : ∀ l, (s.lin l).epoch ≠ 0#W
  /-- `dead` is exactly saturation for lineage cells. -/
  linDeadIffMax : ∀ l, (s.lin l).dead = decide ((s.lin l).epoch = maxE W)
  /-- Lineage cells are always occupied. -/
  linOccupied : ∀ l, (s.lin l).occupied = true
  /-- v1 issues only `lazy` bumps, so no lineage cell is poisoned. -/
  linClean : ∀ l, (s.lin l).poison = false
  /-- The backing store is faithful to the abstract table. -/
  fidelity : ∀ i, s.backing i = s.ent i
  /-- A derivation record never runs ahead of its authorizer's cell. -/
  parentLe : ∀ i j e, (s.ent i).parent = some (j, e) →
    e.toNat ≤ ((s.cell j).epoch).toNat
  /-- While the authorizer's incarnation is the one recorded, the derived
  entry is narrower — no rights amplification. -/
  noAmp : ∀ i j e, (s.ent i).parent = some (j, e) → e = (s.cell j).epoch →
    Narrows (s.ent i) (s.ent j) = true

theorem Init.inv {W N L : Nat} {s : St W N L} (h : Init s) : Inv s where
  cellNonzero := h.cellNonzero
  cellDeadIffMax := h.cellDeadIffMax
  linNonzero := h.linNonzero
  linDeadIffMax := h.linDeadIffMax
  linOccupied := h.linOccupied
  linClean := h.linClean
  fidelity := h.fidelity
  parentLe := fun i _ _ hp => by rw [h.rootless i] at hp; exact absurd hp (by simp)
  noAmp := fun i _ _ hp => by rw [h.rootless i] at hp; exact absurd hp (by simp)

section StepLemmas

variable {W N L : Nat} {s s' : St W N L}

/-- `fill` and `evict` are no-ops on the abstract table, *given* fidelity.
This is the content of T-C6: the fill path cannot introduce authority. -/
theorem fill_ent (hi : Inv s) (i : Fin N)
    (he : stepEv s (.fill i) = some s') : s'.ent = s.ent ∧ s'.cell = s.cell ∧
      s'.backing = s.backing ∧ s'.lin = s.lin := by
  simp only [stepEv] at he
  split at he
  · exact absurd he (by simp)
  · simp only [Option.some.injEq] at he
    subst he
    refine ⟨?_, rfl, rfl, rfl⟩
    dsimp only
    rw [hi.fidelity i, Function.update_eq_self]

theorem evict_backing (hi : Inv s) (i : Fin N)
    (he : stepEv s (.evict i) = some s') : s'.ent = s.ent ∧ s'.cell = s.cell ∧
      s'.backing = s.backing ∧ s'.lin = s.lin := by
  simp only [stepEv] at he
  split at he
  · exact absurd he (by simp)
  · simp only [Option.some.injEq] at he
    subst he
    refine ⟨rfl, rfl, ?_, rfl⟩
    dsimp only
    rw [← hi.fidelity i, Function.update_eq_self]

/-- Embedded epochs are non-decreasing, and death is sticky. -/
theorem step_cell_shape (h : Step s s') (i : Fin N) :
    ((s.cell i).epoch).toNat ≤ ((s'.cell i).epoch).toNat ∧
      ((s.cell i).dead = true → (s'.cell i).dead = true) := by
  obtain ⟨e, he⟩ := h
  cases e with
  | use q => simp only [stepEv, Option.some.injEq] at he; subst he; exact ⟨le_refl _, id⟩
  | fill j =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he; subst he; exact ⟨le_refl _, id⟩
  | evict j =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he; subst he; exact ⟨le_refl _, id⟩
  | drop j =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he
        subst he
        dsimp only
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self]
          exact ⟨Machines.Epoch.Protocol.toNat_le_satInc _, fun hd => by simp [hd]⟩
        · rw [Function.update_of_ne hij]; exact ⟨le_refl _, id⟩
  | revoke l => simp only [stepEv, Option.some.injEq] at he; subst he; exact ⟨le_refl _, id⟩
  | dup a b ed =>
      simp only [stepEv] at he
      split at he
      · simp only [Option.some.injEq] at he
        subst he
        dsimp only
        by_cases hij : i = b
        · subst hij
          rw [Function.update_self]
          exact ⟨Machines.Epoch.Protocol.toNat_le_satInc _, fun hd => by simp [hd]⟩
        · rw [Function.update_of_ne hij]; exact ⟨le_refl _, id⟩
      · exact absurd he (by simp)

theorem step_cell_epoch_mono (h : Step s s') (i : Fin N) :
    ((s.cell i).epoch).toNat ≤ ((s'.cell i).epoch).toNat := (step_cell_shape h i).1

theorem step_cell_dead_sticky (h : Step s s') (i : Fin N)
    (hd : (s.cell i).dead = true) : (s'.cell i).dead = true :=
  (step_cell_shape h i).2 hd

end StepLemmas

/-! ### `Inv` is inductive -/

theorem inv_step {W N L : Nat} {s s' : St W N L} (hi : Inv s) (h : Step s s') :
    Inv s' := by
  obtain ⟨e, he⟩ := h
  cases e with
  | use q => simp only [stepEv, Option.some.injEq] at he; subst he; exact hi
  | fill i =>
      obtain ⟨h1, h2, h3, h4⟩ := fill_ent hi i he
      exact ⟨fun j => by rw [h2]; exact hi.cellNonzero j,
             fun j => by rw [h2]; exact hi.cellDeadIffMax j,
             fun l => by rw [h4]; exact hi.linNonzero l,
             fun l => by rw [h4]; exact hi.linDeadIffMax l,
             fun l => by rw [h4]; exact hi.linOccupied l,
             fun l => by rw [h4]; exact hi.linClean l,
             fun j => by rw [h1, h3]; exact hi.fidelity j,
             fun a b c hp => by rw [h2]; exact hi.parentLe a b c (by rw [h1] at hp; exact hp),
             fun a b c hp hq => by
               rw [h1]
               exact hi.noAmp a b c (by rw [h1] at hp; exact hp) (by rw [h2] at hq; exact hq)⟩
  | evict i =>
      obtain ⟨h1, h2, h3, h4⟩ := evict_backing hi i he
      exact ⟨fun j => by rw [h2]; exact hi.cellNonzero j,
             fun j => by rw [h2]; exact hi.cellDeadIffMax j,
             fun l => by rw [h4]; exact hi.linNonzero l,
             fun l => by rw [h4]; exact hi.linDeadIffMax l,
             fun l => by rw [h4]; exact hi.linOccupied l,
             fun l => by rw [h4]; exact hi.linClean l,
             fun j => by rw [h1, h3]; exact hi.fidelity j,
             fun a b c hp => by rw [h2]; exact hi.parentLe a b c (by rw [h1] at hp; exact hp),
             fun a b c hp hq => by
               rw [h1]
               exact hi.noAmp a b c (by rw [h1] at hp; exact hp) (by rw [h2] at hq; exact hq)⟩
  | drop i =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he
        subst he
        have hcell : ∀ j : Fin N,
            (Function.update s.cell i (Cell.dropped (s.cell i)) j).epoch =
              (if j = i then satInc (s.cell i).epoch else (s.cell j).epoch) := by
          intro j
          rw [Function.update_apply]
          by_cases hji : j = i <;> simp [hji]
        have hdead : ∀ j : Fin N,
            (Function.update s.cell i (Cell.dropped (s.cell i)) j).dead =
              decide ((Function.update s.cell i (Cell.dropped (s.cell i)) j).epoch = maxE W) := by
          intro j
          rw [Function.update_apply]
          by_cases hji : j = i
          · subst hji
            simp only []
            have := bumped_deadIffMax (p := Policy.lazy) (hi.cellDeadIffMax j)
            simpa [Cell.dropped] using this
          · simp only [if_neg hji]; exact hi.cellDeadIffMax j
        refine ⟨?_, hdead, hi.linNonzero, hi.linDeadIffMax, hi.linOccupied, hi.linClean,
          hi.fidelity, ?_, ?_⟩
        · intro j
          rw [hcell j]
          by_cases hji : j = i
          · simp only [if_pos hji]; exact satInc_ne_zero (hi.cellNonzero i)
          · simp only [if_neg hji]; exact hi.cellNonzero j
        · intro a b c hp
          have hb := hi.parentLe a b c hp
          rw [hcell b]
          by_cases hbi : b = i
          · subst hbi
            simp only []
            exact le_trans hb (Machines.Epoch.Protocol.toNat_le_satInc _)
          · simp only [if_neg hbi]; exact hb
        · intro a b c hp hq
          have hb := hi.parentLe a b c hp
          by_cases hbi : b = i
          · subst hbi
            rw [hcell b, if_pos rfl] at hq
            by_cases hd : (s.cell b).dead = true
            · have := satInc_of_dead (hi.cellDeadIffMax b) hd
              rw [this] at hq
              exact hi.noAmp a b c hp hq
            · simp only [Bool.not_eq_true] at hd
              have hs := satInc_strict (hi.cellDeadIffMax b) hd
              rw [hq] at hb
              omega
          · rw [hcell b, if_neg hbi] at hq
            exact hi.noAmp a b c hp hq
  | revoke l =>
      simp only [stepEv, Option.some.injEq] at he
      subst he
      have hlin : ∀ m : Fin L,
          (Function.update s.lin l ((s.lin l).bumped Policy.lazy) m).epoch =
            (if m = l then satInc (s.lin l).epoch else (s.lin m).epoch) := by
        intro m
        rw [Function.update_apply]
        by_cases hml : m = l <;> simp [hml]
      refine ⟨hi.cellNonzero, hi.cellDeadIffMax, ?_, ?_, ?_, ?_, hi.fidelity,
        hi.parentLe, hi.noAmp⟩
      · intro m
        rw [hlin m]
        by_cases hml : m = l
        · simp only [if_pos hml]; exact satInc_ne_zero (hi.linNonzero l)
        · simp only [if_neg hml]; exact hi.linNonzero m
      · intro m
        dsimp only
        rw [Function.update_apply]
        by_cases hml : m = l
        · subst hml; simp only []; exact bumped_deadIffMax (hi.linDeadIffMax m)
        · simp only [if_neg hml]; exact hi.linDeadIffMax m
      · intro m
        dsimp only
        rw [Function.update_apply]
        by_cases hml : m = l
        · subst hml; simp only []
          simpa using hi.linOccupied m
        · simp only [if_neg hml]; exact hi.linOccupied m
      · intro m
        dsimp only
        rw [Function.update_apply]
        by_cases hml : m = l
        · subst hml; simp only []
          simp [hi.linClean m, Machines.Epoch.Protocol.Policy.isPoison]
        · simp only [if_neg hml]; exact hi.linClean m
  | dup src dst ed =>
      simp only [stepEv] at he
      split at he
      · rename_i hg
        simp only [Option.some.injEq] at he
        subst he
        -- unpack the guard
        simp only [dupOk, Bool.and_eq_true, beq_iff_eq] at hg
        obtain ⟨⟨⟨⟨hchk, hocc⟩, hdead⟩, hnar⟩, hpar⟩ := hg
        have hsrcOcc : (s.cell src).occupied = true := (check_ok_iff.mp hchk).2.1
        have hne : src ≠ dst := by
          intro h; rw [h, hocc] at hsrcOcc; exact absurd hsrcOcc (by simp)
        have hcell : ∀ j : Fin N,
            (Function.update s.cell dst (Cell.minted (s.cell dst)) j).epoch =
              (if j = dst then satInc (s.cell dst).epoch else (s.cell j).epoch) := by
          intro j
          rw [Function.update_apply]
          by_cases hjd : j = dst <;> simp [hjd]
        refine ⟨?_, ?_, hi.linNonzero, hi.linDeadIffMax, hi.linOccupied, hi.linClean, ?_, ?_, ?_⟩
        · intro j
          rw [hcell j]
          by_cases hjd : j = dst
          · simp only [if_pos hjd]; exact satInc_ne_zero (hi.cellNonzero dst)
          · simp only [if_neg hjd]; exact hi.cellNonzero j
        · intro j
          dsimp only
          rw [Function.update_apply]
          by_cases hjd : j = dst
          · subst hjd
            simp only []
            have := bumped_deadIffMax (p := Policy.lazy) (hi.cellDeadIffMax j)
            simpa [Cell.minted] using this
          · simp only [if_neg hjd]; exact hi.cellDeadIffMax j
        · intro j
          dsimp only
          rw [Function.update_apply, Function.update_apply]
          by_cases hjd : j = dst
          · simp only [if_pos hjd]
          · simp only [if_neg hjd]; exact hi.fidelity j
        · intro a b c hp
          dsimp only at hp ⊢
          rw [Function.update_apply] at hp
          rw [hcell b]
          by_cases had : a = dst
          · simp only [if_pos had] at hp
            rw [hpar] at hp
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨hb, hc⟩ := hp
            subst hb; subst hc
            rw [if_neg hne]
          · simp only [if_neg had] at hp
            have := hi.parentLe a b c hp
            by_cases hbd : b = dst
            · subst hbd
              simp only []
              exact le_trans this (Machines.Epoch.Protocol.toNat_le_satInc _)
            · simp only [if_neg hbd]; exact this
        · intro a b c hp hq
          dsimp only at hp hq ⊢
          rw [Function.update_apply] at hp
          rw [hcell b] at hq
          by_cases had : a = dst
          · simp only [if_pos had] at hp
            rw [hpar] at hp
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨hb, hc⟩ := hp
            subst hb; subst hc
            rw [Function.update_apply, Function.update_apply, if_pos had, if_neg hne]
            exact hnar
          · simp only [if_neg had] at hp
            have hple := hi.parentLe a b c hp
            by_cases hbd : b = dst
            · subst hbd
              rw [if_pos rfl] at hq
              have hs := satInc_strict (hi.cellDeadIffMax b) hdead
              rw [hq] at hple
              omega
            · rw [if_neg hbd] at hq
              rw [Function.update_apply, Function.update_apply, if_neg had, if_neg hbd]
              exact hi.noAmp a b c hp hq
      · exact absurd he (by simp)

/-- `Inv` is an inductive invariant of the `TSys`. -/
theorem inv_inductive (W N L : Nat) : (sys W N L).Inductive Inv where
  init := fun _ h => Init.inv h
  step := fun _ _ hi h => inv_step hi h

/-- Every reachable state satisfies `Inv`. -/
theorem inv_invariant (W N L : Nat) : (sys W N L).Invariant Inv :=
  (inv_inductive W N L).invariant

section RunLemmas

variable {W N L : Nat}

theorem run_inv {s t : St W N L} (hi : Inv s) (h : Run s t) : Inv t := by
  induction h with
  | refl => exact hi
  | tail _ hst ih => exact inv_step ih hst

theorem run_cell_epoch_mono {s t : St W N L} (h : Run s t) (i : Fin N) :
    ((s.cell i).epoch).toNat ≤ ((t.cell i).epoch).toNat := by
  induction h with
  | refl => exact le_refl _
  | tail _ hst ih => exact le_trans ih (step_cell_epoch_mono hst i)

theorem run_cell_dead_sticky {s t : St W N L} (h : Run s t) (i : Fin N)
    (hd : (s.cell i).dead = true) : (t.cell i).dead = true := by
  induction h with
  | refl => exact hd
  | tail _ hst ih => exact step_cell_dead_sticky hst i ih

end RunLemmas

/-! ## The §3 embedding: lineage cells ARE epoch cells

§2.2: "Both invalidation mechanisms are the same primitive — the slot's
embedded cell (reuse safety) and the shared lineage cell (revocation) are
**epoch cells, §3**. … Saturation semantics, bump policies, and the
reclamation rule are §3's, stated once."

So the lineage half of this protocol is *transported into* §3's mechanized
protocol rather than reproved: `absLin` is the abstraction, `run_absLin` is
the simulation, and T-C4 below is an application of §3's `T_E1_never_ok`. -/

/-- The lineage cells, presented as a settled one-volume §3 epoch system.
One volume: the checking domain reads its own lineage cells locally, and
`cap_revoke`'s bump linearizes (bump/ack/return) before the next check —
which is exactly what makes every lineage read in `check` a post-return
read. -/
def absLin {W N L : Nat} (s : St W N L) : Machines.Epoch.Protocol.St W L 1 where
  cells := s.lin
  repl := fun _ i => (s.lin i).epoch
  pending := none

theorem absLin_inv {W N L : Nat} {s : St W N L} (hi : Inv s) :
    Machines.Epoch.Protocol.Inv (absLin s) where
  deadIffMax := hi.linDeadIffMax
  nonzero := hi.linNonzero
  replLe := fun _ _ => le_refl _
  coherent := fun _ _ _ => rfl
  pendTarget := fun _ hb => absurd hb (by simp [absLin])
  pendAcked := fun _ hb => absurd hb (by simp [absLin])
  pendOther := fun _ hb => absurd hb (by simp [absLin])

theorem absLin_pending {W N L : Nat} (s : St W N L) : (absLin s).pending = none := rfl

/-- A `cap_revoke` is a complete §3 bump/ack/return on the lineage cell. -/
theorem revoke_absLin {W N L : Nat} (s : St W N L) (l : Fin L) :
    Machines.Epoch.Protocol.Run (absLin s)
      (absLin { s with lin := Function.update s.lin l ((s.lin l).bumped Policy.lazy) }) := by
  classical
  set tgt := satInc (s.lin l).epoch with htgt
  set b : Machines.Epoch.Protocol.Bump W L 1 :=
    { cell := l, target := tgt, policy := Policy.lazy, acked := fun _ => false } with hb
  -- state after the bump
  set s1 : Machines.Epoch.Protocol.St W L 1 :=
    { cells := Function.update s.lin l ((s.lin l).bumped Policy.lazy)
      repl := fun _ i => (s.lin i).epoch
      pending := some b } with hs1
  -- state after the ack
  set s2 : Machines.Epoch.Protocol.St W L 1 :=
    { cells := Function.update s.lin l ((s.lin l).bumped Policy.lazy)
      repl := Function.update (fun (_ : Fin 1) (i : Fin L) => (s.lin i).epoch) 0
        (Function.update (fun (i : Fin L) => (s.lin i).epoch) l tgt)
      pending := some { b with acked := Function.update b.acked 0 true } } with hs2
  have e1 : Machines.Epoch.Protocol.stepEv (absLin s)
      (Machines.Epoch.Protocol.Ev.bump l Policy.lazy) = some s1 := by
    simp [Machines.Epoch.Protocol.stepEv, absLin, hs1, hb, htgt]
  have e2 : Machines.Epoch.Protocol.stepEv s1 (Machines.Epoch.Protocol.Ev.ack 0) = some s2 := by
    simp [Machines.Epoch.Protocol.stepEv, hs1, hs2, hb]
  have e3 : Machines.Epoch.Protocol.stepEv s2 Machines.Epoch.Protocol.Ev.bumpReturn =
      some { s2 with pending := none } := by
    simp [Machines.Epoch.Protocol.stepEv, hs2, hb]
  have hrepl : Function.update (fun (_ : Fin 1) (i : Fin L) => (s.lin i).epoch) 0
        (Function.update (fun (i : Fin L) => (s.lin i).epoch) l tgt)
      = fun (_ : Fin 1) (i : Fin L) =>
          ((Function.update s.lin l ((s.lin l).bumped Policy.lazy)) i).epoch := by
    funext k i
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    simp only [Function.update_self, Function.update_apply]
    by_cases hil : i = l
    · subst hil; simp [htgt]
    · simp [hil]
  have hfinal : ({ s2 with pending := none } : Machines.Epoch.Protocol.St W L 1) =
      absLin { s with lin := Function.update s.lin l ((s.lin l).bumped Policy.lazy) } := by
    rw [hs2, hrepl]
    rfl
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single ⟨_, e1⟩) ⟨_, e2⟩) ?_
  exact hfinal ▸ ⟨_, e3⟩

/-- Every capability-protocol step induces a §3 run on the lineage cells.
This is the simulation that lets §3's theorems be *used* here. -/
theorem step_absLin {W N L : Nat} {s s' : St W N L} (h : Step s s') :
    Machines.Epoch.Protocol.Run (absLin s) (absLin s') := by
  obtain ⟨e, he⟩ := h
  cases e with
  | use q => simp only [stepEv, Option.some.injEq] at he; subst he; exact .refl
  | fill i =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he; subst he; exact .refl
  | evict i =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he; subst he; exact .refl
  | drop i =>
      simp only [stepEv] at he
      split at he
      · exact absurd he (by simp)
      · simp only [Option.some.injEq] at he; subst he; exact .refl
  | revoke l =>
      simp only [stepEv, Option.some.injEq] at he
      subst he
      exact revoke_absLin s l
  | dup a b ed =>
      simp only [stepEv] at he
      split at he
      · simp only [Option.some.injEq] at he; subst he; exact .refl
      · exact absurd he (by simp)

theorem run_absLin {W N L : Nat} {s t : St W N L} (h : Run s t) :
    Machines.Epoch.Protocol.Run (absLin s) (absLin t) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.trans (step_absLin hst)

/-! ## The safety theorems (T-C1 … T-C6) -/

namespace Theorems

open Machines.CapWalk.Protocol

variable {W N L : Nat}

/-! ### T-C1 — the null handle is unconstructible as a live handle

§2.2: "**Epoch `0` is architecturally reserved-invalid: every slot's first
live epoch is `1`**, and this makes the null handle an **encoding theorem,
not a convention**: a live handle is `slot << 39 | epoch` with `epoch >= 1`,
so its low 39 bits are nonzero and **the u64 value `0` is unconstructible as
a live handle for any slot**."

Proved from the layout: nothing here is assumed. -/

/-- The layout round-trip: `slot << 39 | epoch` decodes to exactly its
fields, with bit 63 clear. -/
theorem T_C1_layout (sl : BitVec slotBits) (e : BitVec epochBits) :
    hEpoch (mkHandle sl e) = e ∧ hSlot (mkHandle sl e) = sl ∧
      hSign (mkHandle sl e) = false := by
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [hEpoch, mkHandle, epochBits, slotBits, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      Nat.zero_add]
    intro hlt
    have h64 : i < 64 := by omega
    simp [hlt, h64]
  · apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [hSlot, mkHandle, epochBits, slotBits, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    intro hlt
    have h1 : 39 + i < 64 := by omega
    have h2 : i < 64 := by omega
    simp [hlt, h1, h2]
  · simp [hSign, mkHandle, epochBits, slotBits, BitVec.getLsbD_of_ge]

/-- **T-C1.** The `u64` value `0` is unconstructible as a live handle: any
handle whose epoch field is not the reserved `0` differs from `0`. -/
theorem T_C1_null_unconstructible (h : Handle) (hl : Live h) : h ≠ 0#64 := by
  intro hz
  apply hl.2
  rw [hz]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [hEpoch]

/-- **T-C1, constructive half.** Assembling a handle with a live epoch
(`epoch ≥ 1`) never yields `0`, for *any* slot — slot `0` included. -/
theorem T_C1_mkHandle_ne_zero (sl : BitVec slotBits) (e : BitVec epochBits)
    (he : e ≠ 0#epochBits) : mkHandle sl e ≠ 0#64 :=
  T_C1_null_unconstructible _ ⟨(T_C1_layout sl e).2.2, by rw [(T_C1_layout sl e).1]; exact he⟩

/-- The consequence §2.2 draws: "everywhere else handle `0` is simply an
invalid handle and fails `-BADREF` like any other dead handle, never a
special case." Structural, so it holds in every state. -/
theorem T_C1_null_is_badref (s : St epochBits N L) (need : Rights)
    (cls off len : Nat) :
    use s (decode N (0#64) need cls off len) = .badref := by
  have hz : hEpoch (0#64) = 0#epochBits := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp [hEpoch]
  have hwf : (decode N (0#64) need cls off len).wellFormed = false := by
    simp [decode, hz]
  unfold use
  split
  · simp [check, outcome, hwf]
  · rfl

/-- The slot field is a 24-bit index, by construction — §2.2's "sixteen
million slots per domain". -/
theorem T_C1_slot_bounded (h : Handle) : (hSlot h).toNat < 2 ^ slotBits :=
  (hSlot h).isLt

/-! ### T-C2 — the check order

§2.2: "On every *use* the engine checks: slot occupied, handle epoch ==
slot-cell epoch, lineage-cell epoch current, required rights present,
range/class valid. … **Checks occur in that order. No section or operation
may choose a different condition for the same predicate.**" -/

/-- Structural outranks everything: a malformed or out-of-range handle is
`-BADREF` whatever the entry says. -/
theorem T_C2_structural_first (c lc : Cell W) (ed : EntryData W N L) (q : Query W)
    (h : q.wellFormed = false) : check c lc ed q = .badref := by
  simp [check, outcome, h]

/-- §2.2's subtle empty-slot clause: an empty slot is `-STALE`, except that
"**an empty slot whose current embedded epoch nevertheless matches**" is
`-BADREF`. -/
theorem T_C2_empty_slot (c lc : Cell W) (ed : EntryData W N L) (q : Query W)
    (hw : q.wellFormed = true) (ho : c.occupied = false) :
    check c lc ed q = (if c.epoch = q.epoch then .badref else .stale) := by
  simp [check, outcome, hw, ho]

/-- Step 2 outranks steps 3–5: any embedded slot-epoch mismatch is `-STALE`,
whatever the lineage cell, the rights, or the class say. Saturated death is
in the same freshness class (`CAPWALK_SPEC.md` §Deviations, C4). -/
theorem T_C2_embedded_epoch_before_lineage (c lc : Cell W) (ed : EntryData W N L)
    (q : Query W) (hw : q.wellFormed = true) (ho : c.occupied = true)
    (hf : c.epoch ≠ q.epoch ∨ c.dead = true) : check c lc ed q = .stale := by
  rcases hf with h | h
  · simp [check, outcome, hw, ho, h]
  · by_cases he : c.epoch = q.epoch <;> simp [check, outcome, hw, ho, he, h]

/-- Step 3 outranks steps 4–5: a stale lineage stamp is `-STALE` even for a
rights-bearing, in-class, in-range request. -/
theorem T_C2_lineage_before_rights (c lc : Cell W) (ed : EntryData W N L)
    (q : Query W) (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false)
    (hl : linOutcome lc ed ≠ Machines.Epoch.Protocol.Outcome.ok) :
    check c lc ed q = .stale := by
  simp [check, outcome, hw, ho, he, hd, hl]

/-- Step 4 outranks step 5: a live current reference lacking rights is
`-DENIED` even if its class is wrong (which would otherwise be `-BADREF`). -/
theorem T_C2_rights_before_class (c lc : Cell W) (ed : EntryData W N L)
    (q : Query W) (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false)
    (hl : linOutcome lc ed = Machines.Epoch.Protocol.Outcome.ok)
    (hr : rightsSub q.need ed.rights = false) : check c lc ed q = .denied := by
  simp [check, outcome, hw, ho, he, hd, hl, hr]

/-- Step 5, with §2.2's split mapping: a live entry of the wrong
object/interface class is `-BADREF`; a rights-and-class-valid reference
outside the entry's range is `-DENIED`. -/
theorem T_C2_class_and_range_last (c lc : Cell W) (ed : EntryData W N L)
    (q : Query W) (hw : q.wellFormed = true) (ho : c.occupied = true)
    (he : c.epoch = q.epoch) (hd : c.dead = false)
    (hl : linOutcome lc ed = Machines.Epoch.Protocol.Outcome.ok)
    (hr : rightsSub q.need ed.rights = true) :
    check c lc ed q =
      (if ed.cls ≠ q.cls then .badref
       else if rangeIn q.off q.len ed.base ed.len = false then .denied else .ok) := by
  by_cases hc : ed.cls = q.cls
  · by_cases hg : rangeIn q.off q.len ed.base ed.len = true <;>
      simp_all [check, outcome]
  · simp [check, outcome, hw, ho, he, hd, hl, hr, hc]

/-- The priority function, written independently of `outcome`, in §2.2's
prose order. -/
def priority (occ dead : Bool) (cep qep : BitVec 2)
    (wf linFail rightsOk clsOk rangeOk : Bool) : Outcome :=
  if !wf then .badref
  else if !occ then (if cep == qep then .badref else .stale)
  else if (cep != qep) || dead then .stale
  else if linFail then .stale
  else if !rightsOk then .denied
  else if !clsOk then .badref
  else if !rangeOk then .denied
  else .ok

/-- **T-C2.** The stated priority order, re-derived by exhaustive
enumeration at the model's bounds (epoch width 2 — every occupancy, death,
well-formedness, lineage, rights, class and range verdict, and every pair of
epoch values): `2^2 · 2^2 · 2^7 = 2048` local views, checked in the kernel. -/
theorem T_C2_exhaustive :
    ∀ (cep qep : BitVec 2) (occ dead wf linFail rightsOk clsOk rangeOk : Bool),
      outcome occ dead cep qep wf linFail rightsOk clsOk rangeOk =
        priority occ dead cep qep wf linFail rightsOk clsOk rangeOk := by
  decide

/-! ### T-C3 — no rights amplification (the headline)

§2.2: "**New entries are minted only by the engine, only from an authorizing
capability you already hold** (`cap_dup` with monotonically narrowed rights…).
No instruction turns data into authority, and arithmetic on a handle cannot
widen rights." -/

/-- **T-C3.** No reachable state has an entry whose rights exceed its
authorizing entry's. The derivation record is §2.2's `{slot, epoch}` pair,
so the claim is about the incarnation that actually authorized the mint —
see `CAPWALK_SPEC.md` §Deviations, C2. -/
theorem T_C3_no_amplification {s : St W N L}
    (hr : (sys W N L).Reachable s) (i j : Fin N) (e : BitVec W)
    (hp : (s.ent i).parent = some (j, e)) (hq : e = (s.cell j).epoch) :
    rightsSub (s.ent i).rights (s.ent j).rights = true := by
  have hi := inv_invariant W N L s hr
  have := hi.noAmp i j e hp hq
  simp only [Narrows, Bool.and_eq_true] at this
  exact this.1.1.1.1.1

/-- **T-C3, full narrowing.** The same hypothesis gives the whole narrowing
order: rights, range, class, and — crucially for T-C4 — the *same* lineage
cell and stamp, which is why one `cap_revoke` reaches every descendant. -/
theorem T_C3_narrows {s : St W N L}
    (hr : (sys W N L).Reachable s) (i j : Fin N) (e : BitVec W)
    (hp : (s.ent i).parent = some (j, e)) (hq : e = (s.cell j).epoch) :
    Narrows (s.ent i) (s.ent j) = true :=
  (inv_invariant W N L s hr).noAmp i j e hp hq

/-- **T-C3, the datapath half.** "Arithmetic on a handle cannot widen
rights": a successful use never yields authority beyond the entry the slot
holds, for *any* handle value whatsoever. -/
theorem T_C3_no_forge (s : St W N L) (q : Query W) (h : use s q = .ok)
    (hlt : q.slotIx < N) :
    rightsSub q.need (s.ent ⟨q.slotIx, hlt⟩).rights = true := by
  unfold use at h
  rw [dif_pos hlt] at h
  exact (check_ok_iff.mp h).2.2.2.2.2.1

/-- **T-C3, the mint half.** `cap_dup` is *only* enabled when the minted
entry narrows the authorizing one. -/
theorem T_C3_dup_narrows (s s' : St W N L) (src dst : Fin N)
    (ed : EntryData W N L) (h : stepEv s (.dup src dst ed) = some s') :
    Narrows ed (s.ent src) = true := by
  simp only [stepEv] at h
  split at h
  · rename_i hg
    simp only [dupOk, Bool.and_eq_true] at hg
    exact hg.1.2
  · exact absurd h (by simp)

/-! ### T-C4 — revocation reaches every descendant

§2.2: "`cap_revoke` bumps the shared lineage cell **once, O(1)**, and every
entry on the lineage — the original and all derived descendants, in this and
other domains, since they reference the *same* cell — fails its check on next
use. Revocation reaches 'everywhere' not by touching each descendant but by
all descendants sharing one cell."

This is **not** reproved here. The lineage cells are §3 cells (`absLin`),
`cap_revoke` is a complete §3 bump/ack/return (`revoke_absLin`), and the
conclusion is §3's `T_E1_never_ok` transported through `run_absLin`. -/

/-- The lineage verdict `check` consults *is* §3's local check on the
embedded §3 system. -/
theorem linOutcome_eq_epoch_use (s : St W N L) (i : Fin N) :
    linOutcome (s.lin (s.ent i).lineage) (s.ent i) =
      Machines.Epoch.Protocol.use (absLin s) 0 (linReq (s.ent i)) := by
  unfold Machines.Epoch.Protocol.use linOutcome
  have hlt : ((linReq (s.ent i)).cellIx) < L := (s.ent i).lineage.isLt
  rw [dif_pos hlt]
  have : (⟨(linReq (s.ent i)).cellIx, hlt⟩ : Fin L) = (s.ent i).lineage := by
    apply Fin.ext; rfl
  rw [this]
  rfl

/-- The core of T-C4, and the place §3 does the work: after a `cap_revoke`
on lineage cell `l`, **§3's `T_E1_never_ok`** says no reference carrying a
pre-revocation stamp for `l` ever validates again, at any reachable state.
No freshness argument is made here. -/
theorem T_C4_lineage_fails_forever {s s' t : St W N L}
    (hi : Inv s) (l : Fin L)
    (hstep : stepEv s (.revoke l) = some s')
    (hlive : (s.lin l).dead = false)
    (hrun : Run s' t) (i : Fin N)
    (hl : (t.ent i).lineage = l)
    (hstamp : ((t.ent i).linStamp).toNat ≤ ((s.lin l).epoch).toNat) :
    linOutcome (t.lin (t.ent i).lineage) (t.ent i) ≠
      Machines.Epoch.Protocol.Outcome.ok := by
  have hi' : Inv s' := inv_step hi ⟨_, hstep⟩
  have hstrict : ((s.lin l).epoch).toNat < (satInc (s.lin l).epoch).toNat :=
    satInc_strict (hi.linDeadIffMax l) hlive
  have hs'l : (s'.lin l).epoch = satInc (s.lin l).epoch := by
    simp only [stepEv, Option.some.injEq] at hstep
    subst hstep
    simp
  have hne : Machines.Epoch.Protocol.use (absLin t) 0 (linReq (t.ent i)) ≠
      Machines.Epoch.Protocol.Outcome.ok := by
    refine Machines.Epoch.Protocol.Theorems.T_E1_never_ok (absLin_inv hi')
      (absLin_pending _) (run_absLin hrun) l ((t.ent i).linStamp) ?_ 0
      (linReq (t.ent i)) ?_ rfl
    · show ((t.ent i).linStamp).toNat < ((absLin s').cells l).epoch.toNat
      show ((t.ent i).linStamp).toNat < ((s'.lin l)).epoch.toNat
      rw [hs'l]
      omega
    · simp [linReq, hl]
  rw [← linOutcome_eq_epoch_use t i] at hne
  exact hne

/-- **T-C4.** One `cap_revoke` on lineage cell `l` fails *every* entry that
references `l` with a pre-revocation stamp — the original and every
descendant, in every state reachable afterwards, forever. Entries minted
after the revocation inherit their authorizer's stamp (`T_C3_narrows`), so
they are covered too.

The freshness argument is §3's: `Machines.Epoch.Protocol.Theorems.T_E1_never_ok`. -/
theorem T_C4_revocation_reaches_descendants {s s' t : St W N L}
    (hi : Inv s) (l : Fin L)
    (hstep : stepEv s (.revoke l) = some s')
    (hlive : (s.lin l).dead = false)
    (hrun : Run s' t) (i : Fin N)
    (hl : (t.ent i).lineage = l)
    (hstamp : ((t.ent i).linStamp).toNat ≤ ((s.lin l).epoch).toNat)
    (q : Query W) (hq : q.slotIx = i.val) :
    use t q ≠ .ok := by
  have hne := T_C4_lineage_fails_forever hi l hstep hlive hrun i hl hstamp
  unfold use
  have hlt : q.slotIx < N := hq ▸ i.isLt
  rw [dif_pos hlt]
  have hfin : (⟨q.slotIx, hlt⟩ : Fin N) = i := Fin.ext hq
  rw [hfin]
  exact check_ne_ok_of_lineage hne

/-- The sharper form when the reference is otherwise live: the outcome is
exactly `-STALE`, which is §2.2's mapping for "shared lineage/stamp epoch
mismatch". -/
theorem T_C4_revocation_is_stale {s s' t : St W N L}
    (hi : Inv s) (l : Fin L)
    (hstep : stepEv s (.revoke l) = some s')
    (hlive : (s.lin l).dead = false)
    (hrun : Run s' t) (i : Fin N)
    (hl : (t.ent i).lineage = l)
    (hstamp : ((t.ent i).linStamp).toNat ≤ ((s.lin l).epoch).toNat)
    (q : Query W) (hq : q.slotIx = i.val)
    (hw : q.wellFormed = true) (ho : (t.cell i).occupied = true)
    (hep : (t.cell i).epoch = q.epoch) (hd : (t.cell i).dead = false) :
    use t q = .stale := by
  have hne := T_C4_lineage_fails_forever hi l hstep hlive hrun i hl hstamp
  have hlt : q.slotIx < N := hq ▸ i.isLt
  have hfin : (⟨q.slotIx, hlt⟩ : Fin N) = i := Fin.ext hq
  unfold use
  rw [dif_pos hlt, hfin]
  exact T_C2_lineage_before_rights _ _ _ _ hw ho hep hd hne

/-! ### T-C5 — reuse safety

§2.2: "Dropping a slot bumps its embedded cell, **so a stale handle to a
recycled slot fails forever**." -/

/-- **T-C5.** Take the very transition in which slot `i` is dropped. From the
post-drop state onwards — forever, across any number of refills, re-mints and
revocations — no handle carrying the pre-drop epoch validates. -/
theorem T_C5_reuse_safe {s s' t : St W N L} (hi : Inv s) (i : Fin N)
    (hstep : stepEv s (.drop i) = some s') (hrun : Run s' t)
    (q : Query W) (hq : q.slotIx = i.val) (hep : q.epoch = (s.cell i).epoch) :
    use t q ≠ .ok := by
  have hlt : q.slotIx < N := hq ▸ i.isLt
  have hfin : (⟨q.slotIx, hlt⟩ : Fin N) = i := Fin.ext hq
  simp only [stepEv] at hstep
  split at hstep
  · exact absurd hstep (by simp)
  · simp only [Option.some.injEq] at hstep
    subst hstep
    unfold use
    rw [dif_pos hlt, hfin]
    by_cases hd : (s.cell i).dead = true
    · -- a retired slot is dead forever, and a dead cell never validates
      have hdt : (t.cell i).dead = true := by
        refine run_cell_dead_sticky hrun i ?_
        simp [Cell.dropped, hd]
      exact check_ne_ok_of_freshness (Or.inr hdt)
    · -- otherwise the drop strictly advanced the embedded epoch
      simp only [Bool.not_eq_true] at hd
      have hstrict := satInc_strict (hi.cellDeadIffMax i) hd
      have hmono := run_cell_epoch_mono hrun i
      simp only [Function.update_self, Cell.dropped_epoch] at hmono
      refine check_ne_ok_of_freshness (Or.inl ?_)
      intro heq
      rw [hep] at heq
      have hf : ((t.cell i).epoch).toNat = ((s.cell i).epoch).toNat := by rw [heq]
      omega

/-! ### T-C6 — fill fidelity

`CAPWALK_SPEC.md`: "**T-C6 fill fidelity** (a filled entry equals the backing
entry it claims to be — the hook the authenticated store discharges)."
Appendix F row 2's fill path is "a page-walker-class sequencer"; the safety
content is that it installs exactly what the store holds, and that the store
holds exactly the abstract table. -/

/-- The backing store is faithful to the abstract table in every reachable
state. This is the invariant an authenticated backing store must preserve;
v1 has no corruption event (`CAPWALK_SPEC.md` §Deviations, C5). -/
theorem T_C6_store_faithful {s : St W N L} (hr : (sys W N L).Reachable s) (i : Fin N) :
    s.backing i = s.ent i := (inv_invariant W N L s hr).fidelity i

/-- **T-C6.** A fill installs exactly the backing entry it claims to be —
and, given fidelity, the whole abstract table (and therefore every authority
in it) is unchanged by the fill path. The walker cannot introduce authority. -/
theorem T_C6_fill_fidelity {s s' : St W N L} (hi : Inv s) (i : Fin N)
    (he : stepEv s (.fill i) = some s') :
    s'.ent i = s.backing i ∧ s'.ent = s.ent ∧ s'.cell = s.cell ∧ s'.lin = s.lin := by
  refine ⟨?_, (fill_ent hi i he).1, (fill_ent hi i he).2.1, (fill_ent hi i he).2.2.2⟩
  rw [(fill_ent hi i he).1, hi.fidelity i]

/-- Uses are unaffected by residency changes: the fill/evict pair is
observationally neutral, which is what makes the hot cache a cache. -/
theorem T_C6_fill_use_neutral {s s' : St W N L} (hi : Inv s) (i : Fin N)
    (he : stepEv s (.fill i) = some s') (q : Query W) : use s' q = use s q := by
  obtain ⟨h1, h2, _, h4⟩ := fill_ent hi i he
  unfold use
  rw [h1, h2, h4]

/-! ### The model is non-vacuous (a witness, in the style of §3's T-E7)

Every theorem above is a safety statement, so all of them would hold of a
model in which `cap_dup` is never enabled. The run below shows it is: a root
capability in slot 0 mints a narrowed descendant into empty slot 1, the
descendant's handle validates, one `cap_revoke` on the shared lineage cell
then fails it `-STALE`. This is the Layer-4 demo of `CAPWALK_SPEC.md`
§Layers item 4, as a run of `sys 3 2 1`. -/

/-- The root capability: full rights over `[0,16)`, on lineage cell 0. -/
def demoRoot : EntryData 3 2 1 where
  cls := 0
  rights := 255#8
  base := 0
  len := 16
  lineage := 0
  linStamp := 1#3
  sealed := false
  lifetime := Lifetime.persist
  parent := none

/-- The `cap_dup` descendant: narrowed rights and range, same class, same
lineage cell and stamp, derived from slot 0 at epoch 1. -/
def demoChild : EntryData 3 2 1 :=
  { demoRoot with rights := 15#8, base := 4, len := 4, parent := some (0, 1#3) }

/-- Slot 0 occupied by the root, slot 1 empty, one lineage cell at epoch 1. -/
def demoInit : St 3 2 1 where
  cell := fun i =>
    { epoch := 1#3, rc := 0, poison := false, dead := false, occupied := i = 0 }
  ent := fun _ => demoRoot
  backing := fun _ => demoRoot
  resident := fun _ => true
  lin := fun _ =>
    { epoch := 1#3, rc := 1, poison := false, dead := false, occupied := true }

/-- The descendant's handle, presented for a use within its narrowed range. -/
def demoQuery : Query 3 where
  slotIx := 1
  epoch := 2#3
  wellFormed := true
  need := 15#8
  cls := 0
  off := 4
  len := 4

theorem demoInit_init : Init demoInit where
  cellNonzero := by decide
  cellDeadIffMax := by decide
  linNonzero := by decide
  linDeadIffMax := by decide
  linOccupied := by decide
  linClean := by decide
  fidelity := by decide
  rootless := by decide

/-- **Non-vacuity.** `cap_dup` fires, the minted descendant validates, and a
single `cap_revoke` on the shared cell fails it — §2.2's whole story, as one
concrete run. -/
theorem demo_dup_then_revoke :
    ∃ s1 s2 : St 3 2 1,
      Init demoInit ∧
      stepEv demoInit (.dup 0 1 demoChild) = some s1 ∧
      use s1 demoQuery = .ok ∧
      stepEv s1 (.revoke 0) = some s2 ∧
      use s2 demoQuery = .stale := by
  refine ⟨_, _, demoInit_init, rfl, ?_, rfl, ?_⟩
  · decide
  · decide

/-! ### Axiom closures — the 3-axiom kernel closure on every headline. -/

#print axioms T_C1_layout
#print axioms T_C1_null_unconstructible
#print axioms T_C1_mkHandle_ne_zero
#print axioms T_C1_null_is_badref
#print axioms T_C1_slot_bounded
#print axioms T_C2_structural_first
#print axioms T_C2_empty_slot
#print axioms T_C2_embedded_epoch_before_lineage
#print axioms T_C2_lineage_before_rights
#print axioms T_C2_rights_before_class
#print axioms T_C2_class_and_range_last
#print axioms T_C2_exhaustive
#print axioms T_C3_no_amplification
#print axioms T_C3_narrows
#print axioms T_C3_no_forge
#print axioms T_C3_dup_narrows
#print axioms T_C4_revocation_reaches_descendants
#print axioms T_C4_revocation_is_stale
#print axioms T_C5_reuse_safe
#print axioms T_C6_store_faithful
#print axioms T_C6_fill_fidelity
#print axioms T_C6_fill_use_neutral
#print axioms demo_dup_then_revoke

end Theorems
end Machines.CapWalk.Protocol
