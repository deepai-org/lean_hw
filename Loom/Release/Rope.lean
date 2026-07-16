-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

/-!
# Balanced release-artifact ropes

Large generated RTL must never be normalized as one monolithic Lean `String`.
`Rope` keeps both artifact data and equality proofs balanced. Release generators
emit bounded leaves as separate declarations; internal nodes refer to those
named theorem constants and compose them by congruence.

The final byte statement is obtained abstractly with `congrArg flattenBytes`.
The kernel therefore checks the equality proof without evaluating the complete
concatenated file. CI independently binds the ordered leaf payloads to the file
on disk using exact `cmp`.
-/

namespace Loom.Release

universe u v

/-- A nonempty balanced binary tree. Release artifacts use bounded lists of
logical lines at leaves. -/
inductive Rope (α : Type u) where
  | leaf (value : α)
  | node (left right : Rope α)
  deriving Repr, DecidableEq

/-- Apply a function independently at every leaf while preserving shape. -/
def Rope.map {α : Type u} {β : Type v} (f : α → β) : Rope α → Rope β
  | .leaf value => .leaf (f value)
  | .node left right => .node (left.map f) (right.map f)

@[simp] theorem Rope.map_leaf {α : Type u} {β : Type v}
    (f : α → β) (value : α) :
    (Rope.leaf value).map f = .leaf (f value) := rfl

@[simp] theorem Rope.map_node {α : Type u} {β : Type v}
    (f : α → β) (left right : Rope α) :
    (Rope.node left right).map f = .node (left.map f) (right.map f) := rfl

/-- Concatenate list-valued leaves in left-to-right order. This function is
used in theorem statements; full release proofs do not normalize it. -/
def Rope.flattenLists {α : Type u} : Rope (List α) → List α
  | .leaf values => values
  | .node left right => left.flattenLists ++ right.flattenLists

/-- Number of list elements stored across all leaves, without flattening. -/
def Rope.listLength {α : Type u} : Rope (List α) → Nat
  | .leaf values => values.length
  | .node left right => left.listLength + right.listLength

/-- Index a list-valued rope directly. This keeps large initialization images
balanced in both the witness and its elaborated memory function. -/
def Rope.getD {α : Type u} (rope : Rope (List α)) (index : Nat)
    (fallback : α) : α :=
  match rope with
  | .leaf values => values.getD index fallback
  | .node left right =>
      if index < left.listLength then left.getD index fallback
      else right.getD (index - left.listLength) fallback

/-- Map list leaves while supplying each leaf's starting element offset. -/
def Rope.mapWithOffset {α : Type u} {β : Type v}
    (f : Nat → List α → List β) (start : Nat) :
    Rope (List α) → Rope (List β)
  | .leaf values => .leaf (f start values)
  | .node left right =>
      .node (left.mapWithOffset f start)
        (right.mapWithOffset f (start + left.listLength))

/-- Interpret a line rope as exact file bytes: LF between logical lines and no
additional transformation. A trailing empty final line therefore represents a
file ending in LF. -/
def Rope.flattenBytes (rope : Rope (List String)) : String :=
  String.intercalate "\n" rope.flattenLists

/-- Map equal leaf payloads through an arbitrary renderer. This is the generic
form used by generated named internal proof nodes. -/
theorem Rope.node_congr {α : Type u} {leftA leftB rightA rightB : Rope α}
    (hl : leftA = leftB) (hr : rightA = rightB) :
    Rope.node leftA rightA = Rope.node leftB rightB := by
  cases hl
  cases hr
  rfl

/-- Equal line ropes denote byte-identical streams. Crucially this proof is
pure congruence: it does not reduce `flattenBytes`. -/
theorem Rope.flattenBytes_congr {a b : Rope (List String)} (h : a = b) :
    a.flattenBytes = b.flattenBytes := congrArg Rope.flattenBytes h

/-- A release witness supplies some item type together with a structural
renderer into bounded line leaves. -/
structure Rendered (Item : Type u) where
  witness : Rope Item
  disk : Rope (List String)

/-- Render every witness leaf without flattening the complete artifact. -/
def Rendered.renderTree {Item : Type u} (renderItem : Item → List String)
    (artifact : Rendered Item) : Rope (List String) :=
  artifact.witness.map renderItem

/-- The exact-byte conclusion used by release theorems. Generated code proves
`renderTree = disk` from separately named bounded leaf theorems, then invokes
this lemma once at the root. -/
theorem Rendered.exactBytes {Item : Type u} (renderItem : Item → List String)
    (artifact : Rendered Item)
    (h : artifact.renderTree renderItem = artifact.disk) :
    (artifact.renderTree renderItem).flattenBytes =
      artifact.disk.flattenBytes :=
  Rope.flattenBytes_congr h

end Loom.Release
