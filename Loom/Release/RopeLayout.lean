-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Batteries.Tactic.OpenPrivate
import Loom.Release.ToProgramLemmas

/-!
# Layout lemmas for `toProgram_wireWellFormed`

The layout half of the wire-table well-formedness theorem: the constructed
witness rope (`shapeWireRope` / `Design.indexedsOf`) answers every
`Symbolic.lookupIndexed?` query with the wire the flat list holds at that
number. Three independent facts compose:

* **Collapse** (`balancedRope_chunks_pow2`): grouping leaves into
  `2 ^ k`-sized chunks, balancing each chunk, and balancing the chunk roots
  builds *literally the same tree* as balancing the leaves directly. The
  power-of-two hypothesis is essential — it keeps chunk fronts even-length
  through every pairing round.
* **Path correctness** (`balancedRope_resolve_path`): the root-to-leaf paths
  computed by `Symbolic.balancedPath?` resolve to the correct leaf block in
  `balancedRope`, for every leaf count.
* **Chunk arithmetic** (`listChunks_getElem`, `listChunks_length`): dividing
  the wire number by the leaf size selects the chunk and offset holding it.

The corollary `lookupIndexed?_shaped` discharges the lookup conjunct for the
default witness shape (`blockSize` leaves, `chunkLeaves = 16 = 2 ^ 4` leaves
per chunk tree).
-/

namespace Loom.Release.SSA

open Loom.Release.Symbolic

open private balancedPathAux from Loom.Release.SymbolicCertificate

/-! ## `pairStep` basics -/

theorem pairStep_nil {α : Type} : pairStep ([] : List (Rope α)) = [] := rfl

theorem pairStep_singleton {α : Type} (r : Rope α) : pairStep [r] = [r] := rfl

theorem pairStep_cons_cons {α : Type} (one two : Rope α)
    (rest : List (Rope α)) :
    pairStep (one :: two :: rest) = .node one two :: pairStep rest := rfl

theorem pairStep_length {α : Type} :
    ∀ (items : List (Rope α)), (pairStep items).length = (items.length + 1) / 2
  | [] => by simp [pairStep_nil]
  | [r] => by simp [pairStep_singleton]
  | _ :: _ :: rest => by
      rw [pairStep_cons_cons]
      simp only [List.length_cons, pairStep_length rest]
      omega

/-- Pairing distributes over an append whose front has even length. This is
what keeps `2 ^ k`-aligned chunk boundaries intact through every round. -/
theorem pairStep_append {α : Type} :
    ∀ (a b : List (Rope α)), a.length % 2 = 0 →
      pairStep (a ++ b) = pairStep a ++ pairStep b
  | [], _, _ => rfl
  | [_], _, even => by simp at even
  | x :: y :: t, b, even => by
      have : t.length % 2 = 0 := by
        simp only [List.length_cons] at even
        omega
      simp only [List.cons_append, pairStep_cons_cons,
        pairStep_append t b this]

/-- Element `i` of the list becomes side `i % 2` of node `i / 2` after one
pairing round (fully paired case). -/
theorem pairStep_getElem?_pair {α : Type} :
    ∀ (items : List (Rope α)) (j : Nat) (a b : Rope α),
      items[2 * j]? = some a → items[2 * j + 1]? = some b →
      (pairStep items)[j]? = some (.node a b)
  | [], _, _, _, ha, _ => by simp at ha
  | [_], _, _, _, _, hb => by simp at hb
  | x :: y :: t, 0, a, b, ha, hb => by
      simp only [Nat.mul_zero, List.getElem?_cons_zero, Nat.zero_add,
        List.getElem?_cons_succ, Option.some.injEq] at ha hb
      rw [pairStep_cons_cons, List.getElem?_cons_zero, ha, hb]
  | x :: y :: t, j + 1, a, b, ha, hb => by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
        List.getElem?_cons_succ, List.getElem?_cons_succ] at ha
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by omega,
        List.getElem?_cons_succ, List.getElem?_cons_succ] at hb
      rw [pairStep_cons_cons, List.getElem?_cons_succ]
      exact pairStep_getElem?_pair t j a b ha hb

/-- The odd trailing element is promoted unchanged: on a list of length
`2 * j + 1` it stays at position `j` after the round. -/
theorem pairStep_getElem?_last {α : Type} :
    ∀ (items : List (Rope α)) (j : Nat) (a : Rope α),
      items.length = 2 * j + 1 → items[2 * j]? = some a →
      (pairStep items)[j]? = some a
  | [], _, _, hlen, _ => by simp at hlen
  | [x], j, a, hlen, ha => by
      have hj : j = 0 := by
        simp only [List.length_cons, List.length_nil] at hlen
        omega
      subst hj
      simpa [pairStep_singleton] using ha
  | x :: y :: t, j, a, hlen, ha => by
      match j with
      | 0 => simp at hlen
      | j' + 1 =>
          have hlen' : t.length = 2 * j' + 1 := by
            simp only [List.length_cons] at hlen
            omega
          rw [show 2 * (j' + 1) = 2 * j' + 1 + 1 by omega,
            List.getElem?_cons_succ, List.getElem?_cons_succ] at ha
          rw [pairStep_cons_cons, List.getElem?_cons_succ]
          exact pairStep_getElem?_last t j' a hlen' ha

/-! ## Fuel irrelevance for `balancedGo` -/

theorem balancedGo_congr {α : Type} [Inhabited α] :
    ∀ (f g : Nat) (items : List (Rope α)), items.length ≤ f →
      items.length ≤ g → balancedGo f items = balancedGo g items
  | f, g, [], _, _ => by cases f <;> cases g <;> rfl
  | f, g, [r], _, _ => by cases f <;> cases g <;> rfl
  | 0, _, _ :: _ :: _, hf, _ => by simp at hf
  | _ + 1, 0, _ :: _ :: _, _, hg => by simp at hg
  | f + 1, g + 1, x :: y :: t, hf, hg => by
      show balancedGo f (pairStep (x :: y :: t)) =
        balancedGo g (pairStep (x :: y :: t))
      have hlen : (pairStep (x :: y :: t)).length = (t.length + 3) / 2 := by
        rw [pairStep_length]
        simp only [List.length_cons]
      simp only [List.length_cons] at hf hg
      exact balancedGo_congr f g _ (by omega) (by omega)

/-- One pairing round never changes the balanced result: `balancedGo` with
full fuel just iterates `pairStep` until a single tree remains. -/
theorem balancedRope_pairStep {α : Type} [Inhabited α] :
    ∀ (items : List (Rope α)),
      balancedRope (pairStep items) = balancedRope items
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
      have step : balancedRope (x :: y :: t) =
          balancedGo (t.length + 1) (pairStep (x :: y :: t)) := rfl
      rw [step]
      show balancedGo (pairStep (x :: y :: t)).length _ = _
      refine balancedGo_congr _ _ _ (Nat.le_refl _) ?_
      rw [pairStep_length]
      simp only [List.length_cons]
      omega

/-! ## Iterated pairing -/

/-- `k` rounds of pairing. -/
def pairIter {α : Type} : Nat → List (Rope α) → List (Rope α)
  | 0, items => items
  | k + 1, items => pairIter k (pairStep items)

theorem pairIter_nil {α : Type} :
    ∀ (k : Nat), pairIter k ([] : List (Rope α)) = []
  | 0 => rfl
  | k + 1 => pairIter_nil k

theorem balancedRope_pairIter {α : Type} [Inhabited α] :
    ∀ (k : Nat) (items : List (Rope α)),
      balancedRope (pairIter k items) = balancedRope items
  | 0, _ => rfl
  | k + 1, items => by
      show balancedRope (pairIter k (pairStep items)) = _
      rw [balancedRope_pairIter k, balancedRope_pairStep]

theorem pairIter_append {α : Type} :
    ∀ (k : Nat) (a b : List (Rope α)), a.length = 2 ^ k →
      pairIter k (a ++ b) = pairIter k a ++ pairIter k b
  | 0, _, _, _ => rfl
  | k + 1, a, b, hlen => by
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      show pairIter k (pairStep (a ++ b)) =
        pairIter k (pairStep a) ++ pairIter k (pairStep b)
      rw [pairStep_append a b (by omega),
        pairIter_append k _ _ (by rw [pairStep_length, hlen]; omega)]

/-- A nonempty list that fits into one `2 ^ k` chunk collapses to its own
balanced tree after `k` rounds. -/
theorem pairIter_small {α : Type} [Inhabited α] :
    ∀ (k : Nat) (items : List (Rope α)), items ≠ [] →
      items.length ≤ 2 ^ k → pairIter k items = [balancedRope items]
  | 0, [], hne, _ => absurd rfl hne
  | 0, [_], _, _ => rfl
  | 0, _ :: _ :: _, _, hlen => by simp at hlen
  | k + 1, items, hne, hlen => by
      have hpos : 0 < items.length := List.length_pos_iff.mpr hne
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
      have hpslen : (pairStep items).length = (items.length + 1) / 2 :=
        pairStep_length items
      show pairIter k (pairStep items) = _
      rw [pairIter_small k (pairStep items)
          (List.ne_nil_of_length_pos (by omega)) (by omega),
        balancedRope_pairStep]

/-! ## `listChunks` bookkeeping -/

theorem listChunksGo_congr {α : Type} {size : Nat} (positive : 0 < size) :
    ∀ (f g : Nat) (items : List α), items.length ≤ f → items.length ≤ g →
      listChunksGo size f items = listChunksGo size g items
  | f, g, [], _, _ => by cases f <;> cases g <;> rfl
  | 0, _, _ :: _, hf, _ => by simp at hf
  | _ + 1, 0, _ :: _, _, hg => by simp at hg
  | f + 1, g + 1, x :: t, hf, hg => by
      show (x :: t).take size :: listChunksGo size f ((x :: t).drop size) =
        (x :: t).take size :: listChunksGo size g ((x :: t).drop size)
      simp only [List.length_cons] at hf hg
      have hdrop : ((x :: t).drop size).length = t.length + 1 - size := by
        simp only [List.length_drop, List.length_cons]
      exact congrArg _ (listChunksGo_congr positive f g _
        (by omega) (by omega))

theorem listChunks_nil {α : Type} {size : Nat} (positive : 0 < size) :
    listChunks size ([] : List α) = [] := by
  unfold listChunks
  rw [if_neg (by omega)]
  rfl

theorem listChunks_cons {α : Type} {size : Nat} (positive : 0 < size)
    (x : α) (rest : List α) :
    listChunks size (x :: rest) =
      (x :: rest).take size :: listChunks size ((x :: rest).drop size) := by
  unfold listChunks
  rw [if_neg (by omega), if_neg (by omega)]
  show (x :: rest).take size ::
      listChunksGo size rest.length ((x :: rest).drop size) = _
  refine congrArg _ (listChunksGo_congr positive _ _ _ ?_ (Nat.le_refl _))
  simp only [List.length_drop, List.length_cons]
  omega

theorem listChunks_length_go {α : Type} {size : Nat} (positive : 0 < size) :
    ∀ (fuel : Nat) (items : List α), items.length ≤ fuel →
      (listChunks size items).length = (items.length + size - 1) / size
  | _, [], _ => by
      rw [listChunks_nil positive]
      simp only [List.length_nil, Nat.zero_add]
      exact (Nat.div_eq_of_lt (by omega)).symm
  | 0, _ :: _, bound => by simp at bound
  | fuel + 1, x :: t, bound => by
      simp only [List.length_cons] at bound
      rw [listChunks_cons positive, List.length_cons,
        listChunks_length_go positive fuel ((x :: t).drop size)
          (by simp only [List.length_drop, List.length_cons]; omega)]
      simp only [List.length_drop, List.length_cons]
      by_cases hle : t.length + 1 ≤ size
      · rw [show t.length + 1 - size = 0 by omega,
          Nat.div_eq_of_lt (by omega),
          show t.length + 1 + size - 1 = t.length + size by omega,
          Nat.add_div_right _ positive, Nat.div_eq_of_lt (by omega)]
      · rw [show t.length + 1 - size + size - 1 =
            t.length - size + size by omega,
          show t.length + 1 + size - 1 =
            t.length - size + size + size by omega,
          Nat.add_div_right _ positive, Nat.add_div_right _ positive,
          Nat.add_div_right _ positive]

/-- The chunk count is the rounded-up quotient. -/
theorem listChunks_length {α : Type} (size : Nat) (positive : 0 < size)
    (items : List α) :
    (listChunks size items).length = (items.length + size - 1) / size :=
  listChunks_length_go positive items.length items (Nat.le_refl _)

theorem listChunks_getElem_go {α : Type} {size : Nat} (positive : 0 < size) :
    ∀ (fuel : Nat) (items : List α), items.length ≤ fuel → ∀ (n : Nat),
      ((listChunks size items)[n / size]?.getD [])[n % size]? = items[n]?
  | _, [], _, n => by rw [listChunks_nil positive]; simp
  | 0, _ :: _, bound, _ => by simp at bound
  | fuel + 1, x :: t, bound, n => by
      simp only [List.length_cons] at bound
      rw [listChunks_cons positive]
      by_cases hn : n < size
      · rw [Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn,
          List.getElem?_cons_zero, Option.getD_some]
        exact List.getElem?_take_of_lt hn
      · have hdiv : n / size = (n - size) / size + 1 :=
          Nat.div_eq_sub_div positive (by omega)
        have hmod : n % size = (n - size) % size :=
          Nat.mod_eq_sub_mod (by omega)
        rw [hdiv, hmod, List.getElem?_cons_succ,
          listChunks_getElem_go positive fuel ((x :: t).drop size)
            (by simp only [List.length_drop, List.length_cons]; omega)
            (n - size),
          List.getElem?_drop, show size + (n - size) = n by omega]

/-- Chunk indexing arithmetic: element `n` of the flat list is element
`n % size` of chunk `n / size`. -/
theorem listChunks_getElem {α : Type} (s : Nat) (hs : 0 < s) (xs : List α)
    (n : Nat) :
    ((listChunks s xs)[n / s]?.getD [])[n % s]? = xs[n]? :=
  listChunks_getElem_go hs xs.length xs (Nat.le_refl _) n

/-! ## The collapse lemma -/

theorem pairIter_chunks {α : Type} [Inhabited α] (k : Nat) :
    ∀ (fuel : Nat) (leaves : List (Rope α)), leaves.length ≤ fuel →
      pairIter k leaves = (listChunks (2 ^ k) leaves).map balancedRope
  | _, [], _ => by
      rw [pairIter_nil, listChunks_nil (Nat.two_pow_pos k),
        List.map_nil]
  | 0, _ :: _, bound => by simp at bound
  | fuel + 1, x :: t, bound => by
      have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
      simp only [List.length_cons] at bound
      rw [listChunks_cons hpow]
      by_cases hle : (x :: t).length ≤ 2 ^ k
      · rw [List.take_of_length_le hle, List.drop_eq_nil_of_le hle,
          listChunks_nil hpow, List.map_cons, List.map_nil]
        exact pairIter_small k (x :: t) (List.cons_ne_nil x t) hle
      · have htake : ((x :: t).take (2 ^ k)).length = 2 ^ k := by
          rw [List.length_take]
          simp only [List.length_cons] at hle ⊢
          omega
        conv => lhs; rw [← List.take_append_drop (2 ^ k) (x :: t)]
        rw [pairIter_append k _ _ htake,
          pairIter_small k _ (List.ne_nil_of_length_pos (by omega))
            (Nat.le_of_eq htake),
          pairIter_chunks k fuel ((x :: t).drop (2 ^ k))
            (by simp only [List.length_drop, List.length_cons]; omega),
          List.map_cons, List.singleton_append]

/-- **Collapse**: balancing `2 ^ k`-sized balanced chunks builds literally
the same tree as balancing the leaves directly. -/
theorem balancedRope_chunks_pow2 {α : Type} [Inhabited α] (k : Nat)
    (leaves : List (Rope α)) :
    balancedRope ((listChunks (2 ^ k) leaves).map balancedRope) =
      balancedRope leaves := by
  rw [← pairIter_chunks k leaves.length leaves (Nat.le_refl _),
    balancedRope_pairIter]

/-! ## Fuel-free view of `balancedPath?` -/

/-- Fuel-free specification of the private `balancedPathAux`: recursion on
the parent round `(count + 1) / 2` at index `index / 2`, appending the child
side except for the odd promoted last element. -/
def pathSpec : Nat → Nat → Option (List Bool)
  | 0, _ => none
  | 1, 0 => some []
  | 1, _ + 1 => none
  | count + 2, index =>
      (pathSpec ((count + 2 + 1) / 2) (index / 2)).map fun parent =>
        if (count + 2) % 2 == 1 && index + 1 == count + 2 then parent
        else parent ++ [index % 2 == 1]
termination_by count _ => count
decreasing_by omega

theorem balancedPathAux_eq_pathSpec :
    ∀ (fuel count index : Nat), count ≤ fuel →
      balancedPathAux fuel count index = pathSpec count index
  | fuel, 0, index, _ => by cases fuel <;> simp [pathSpec, balancedPathAux]
  | fuel + 1, 1, 0, _ => by
      simp only [pathSpec]
      rfl
  | fuel + 1, 1, _ + 1, _ => by
      simp only [pathSpec]
      rfl
  | 0, 1, _, bound => by omega
  | 0, _ + 2, _, bound => by omega
  | fuel + 1, count + 2, index, bound => by
      rw [show balancedPathAux (fuel + 1) (count + 2) index =
            (balancedPathAux fuel ((count + 2 + 1) / 2) (index / 2)).bind
              fun parent =>
                if (count + 2) % 2 == 1 && index + 1 == count + 2 then
                  pure parent
                else pure (parent ++ [index % 2 == 1]) from rfl,
        balancedPathAux_eq_pathSpec fuel ((count + 2 + 1) / 2) (index / 2)
          (by omega)]
      rw [pathSpec]
      cases pathSpec ((count + 2 + 1) / 2) (index / 2) with
      | none => rfl
      | some parent => split <;> rfl

theorem balancedPath?_eq_pathSpec (count index : Nat) (h : index < count) :
    balancedPath? count index = pathSpec count index := by
  unfold balancedPath?
  simp only [guard, if_pos h]
  show balancedPathAux (count + 1) count index = pathSpec count index
  exact balancedPathAux_eq_pathSpec (count + 1) count index (by omega)

theorem lt_of_balancedPath?_eq_some {count index : Nat} {path : List Bool}
    (found : balancedPath? count index = some path) : index < count := by
  cases Nat.lt_or_ge index count with
  | inl h => exact h
  | inr h =>
      unfold balancedPath? at found
      simp only [guard, if_neg (Nat.not_lt.mpr h)] at found
      exact nomatch (show (none : Option (List Bool)) = some path from found)

/-- Completeness: every in-range index has a balanced path. -/
theorem pathSpec_isSome :
    ∀ (count index : Nat), index < count →
      (pathSpec count index).isSome = true
  | 0, _, h => by omega
  | 1, 0, _ => by simp [pathSpec]
  | 1, _ + 1, h => by omega
  | count + 2, index, h => by
      have ih := pathSpec_isSome ((count + 2 + 1) / 2) (index / 2) (by omega)
      rw [pathSpec]
      cases hp : pathSpec ((count + 2 + 1) / 2) (index / 2) with
      | none => rw [hp] at ih; simp at ih
      | some parent => rfl
termination_by count _ => count
decreasing_by omega

theorem balancedPath?_isSome (count index : Nat) (h : index < count) :
    (balancedPath? count index).isSome = true := by
  rw [balancedPath?_eq_pathSpec count index h]
  exact pathSpec_isSome count index h

/-! ## Path correctness for `balancedRope` -/

theorem balancedRope_resolve_go {α : Type} :
    ∀ (fuel : Nat) (ropes : List (Rope (List α))), ropes.length ≤ fuel →
      ∀ (i : Nat), i < ropes.length →
      ∀ (path rest : List Bool) (offset : Nat),
        pathSpec ropes.length i = some path →
        (balancedRope ropes).resolve? ⟨path ++ rest, offset⟩ =
          (ropes[i]?.getD (Rope.leaf [])).resolve? ⟨rest, offset⟩
  | _, [], _, i, hi, _, _, _, _ => by simp at hi
  | _, [r], _, i, hi, path, rest, offset, found => by
      have hi0 : i = 0 := by
        simp only [List.length_cons, List.length_nil] at hi
        omega
      subst hi0
      have hpath : path = [] := by
        simp only [List.length_cons, List.length_nil, Nat.zero_add,
          pathSpec, Option.some.injEq] at found
        exact found.symm
      subst hpath
      rw [List.nil_append]
      rfl
  | 0, _ :: _ :: _, hf, _, _, _, _, _, _ => by simp at hf
  | fuel + 1, x :: y :: t, hf, i, hi, path, rest, offset, found => by
      simp only [List.length_cons] at hi hf found
      rw [show t.length + 1 + 1 = t.length + 2 by omega] at found
      simp only [pathSpec, Option.map_eq_some_iff] at found
      obtain ⟨parent, hparent, hpath⟩ := found
      have hrope : balancedRope (x :: y :: t) =
          balancedRope (pairStep (x :: y :: t)) :=
        (balancedRope_pairStep _).symm
      have hpslen : (pairStep (x :: y :: t)).length =
          (t.length + 2 + 1) / 2 := by
        rw [pairStep_length]
        simp only [List.length_cons]
      have hfuel : (pairStep (x :: y :: t)).length ≤ fuel := by
        rw [hpslen]; omega
      have hi2 : i / 2 < (pairStep (x :: y :: t)).length := by
        rw [hpslen]; omega
      have hparent' :
          pathSpec (pairStep (x :: y :: t)).length (i / 2) = some parent := by
        rw [hpslen]; exact hparent
      by_cases hcond :
          ((t.length + 2) % 2 == 1 && i + 1 == t.length + 2) = true
      · rw [if_pos hcond] at hpath
        subst hpath
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hodd, hlast⟩ := hcond
        rw [hrope, balancedRope_resolve_go fuel _ hfuel (i / 2) hi2
          parent rest offset hparent']
        cases ha : (x :: y :: t)[i]? with
        | none =>
            rw [List.getElem?_eq_none_iff] at ha
            simp only [List.length_cons] at ha
            omega
        | some a =>
            have ha2 : (x :: y :: t)[2 * (i / 2)]? = some a := by
              rw [show 2 * (i / 2) = i by omega]
              exact ha
            rw [pairStep_getElem?_last (x :: y :: t) (i / 2) a
              (by simp only [List.length_cons]; omega) ha2]
      · rw [if_neg hcond] at hpath
        subst hpath
        simp only [Bool.and_eq_true, beq_iff_eq, not_and] at hcond
        have hbound : 2 * (i / 2) + 1 < t.length + 2 := by
          by_cases hlast : i + 1 = t.length + 2
          · have : ¬ (t.length + 2) % 2 = 1 := fun hodd =>
              hcond hodd hlast
            omega
          · omega
        rw [List.append_assoc, List.singleton_append, hrope,
          balancedRope_resolve_go fuel _ hfuel (i / 2) hi2 parent
            ((i % 2 == 1) :: rest) offset hparent']
        cases ha : (x :: y :: t)[2 * (i / 2)]? with
        | none =>
            rw [List.getElem?_eq_none_iff] at ha
            simp only [List.length_cons] at ha
            omega
        | some a =>
        cases hb : (x :: y :: t)[2 * (i / 2) + 1]? with
        | none =>
            rw [List.getElem?_eq_none_iff] at hb
            simp only [List.length_cons] at hb
            omega
        | some b =>
        rw [pairStep_getElem?_pair _ _ _ _ ha hb, Option.getD_some]
        rcases Nat.mod_two_eq_zero_or_one i with heven | hodd
        · rw [show (i % 2 == 1) = false by rw [heven]; rfl,
            Rope.resolve_node_left,
            show i = 2 * (i / 2) by omega, ha, Option.getD_some]
        · rw [show (i % 2 == 1) = true by rw [hodd]; rfl,
            Rope.resolve_node_right,
            show i = 2 * (i / 2) + 1 by omega, hb, Option.getD_some]

/-- **Path correctness**: the path `balancedPath?` computes for block `i`
resolves in `balancedRope` to element `offset` of block `i`. -/
theorem balancedRope_resolve_path {α : Type} (blocks : List (List α))
    (i : Nat) (path : List Bool)
    (found : Loom.Release.Symbolic.balancedPath? blocks.length i = some path)
    (offset : Nat) :
    (balancedRope (blocks.map Rope.leaf)).resolve? ⟨path, offset⟩ =
      (blocks[i]?.getD [])[offset]? := by
  have hi : i < blocks.length := lt_of_balancedPath?_eq_some found
  rw [balancedPath?_eq_pathSpec _ _ hi] at found
  have hmap : (blocks.map Rope.leaf).length = blocks.length :=
    List.length_map ..
  have resolved := balancedRope_resolve_go (blocks.map Rope.leaf).length
    (blocks.map Rope.leaf) (Nat.le_refl _) i (by rw [hmap]; exact hi)
    path [] offset (by rw [hmap]; exact found)
  rw [List.append_nil] at resolved
  rw [resolved]
  cases hb : blocks[i]? with
  | none =>
      rw [List.getElem?_eq_none_iff] at hb
      omega
  | some block =>
      rw [List.getElem?_map, hb, Option.map_some, Option.getD_some,
        Option.getD_some, Rope.resolve_leaf]

/-! ## The layout corollary -/

/-- **Layout half of `toProgram_wireWellFormed`**: on the witness shape —
`leafSize`-sized leaves, `2 ^ k` leaves per balanced chunk tree, balanced
root — `lookupIndexed?` answers every query with the wire the flat list
holds at that number. -/
theorem lookupIndexed?_shaped (k : Nat) (leafSize : Nat) (hs : 0 < leafSize)
    (xs : List Loom.Release.Symbolic.IndexedWire)
    (hnum : ∀ (i : Nat) (wire : Loom.Release.Symbolic.IndexedWire),
      xs[i]? = some wire → wire.number = i)
    (n : Nat) (wire : Loom.Release.Symbolic.IndexedWire)
    (hfound : xs[n]? = some wire) :
    Loom.Release.Symbolic.lookupIndexed?
      (balancedRope
        ((listChunks (2 ^ k) ((listChunks leafSize xs).map Rope.leaf)).map
          balancedRope))
      { leafSize := leafSize,
        leafCount := (xs.length + leafSize - 1) / leafSize }
      n = some wire := by
  have hn : n < xs.length := by
    cases Nat.lt_or_ge n xs.length with
    | inl h => exact h
    | inr h =>
        rw [List.getElem?_eq_none_iff.mpr h] at hfound
        exact nomatch hfound
  have hcount : n / leafSize < (xs.length + leafSize - 1) / leafSize := by
    rw [show xs.length + leafSize - 1 = xs.length - 1 + leafSize by omega,
      Nat.add_div_right _ hs]
    have := Nat.div_le_div_right (c := leafSize)
      (show n ≤ xs.length - 1 by omega)
    omega
  obtain ⟨path, hpath⟩ :=
    Option.isSome_iff_exists.mp (balancedPath?_isSome _ _ hcount)
  refine Symbolic.lookupIndexed_of_resolve hs hpath ?_ (hnum n wire hfound)
  show (balancedRope _).resolve? ⟨path, n % leafSize⟩ = some wire
  rw [balancedRope_chunks_pow2,
    balancedRope_resolve_path (listChunks leafSize xs) (n / leafSize) path
      (by rw [listChunks_length leafSize hs xs]; exact hpath) (n % leafSize),
    listChunks_getElem leafSize hs xs n]
  exact hfound

/-! ## Evidence introduction for the witness shape

The two inductive rope predicates consumed by
`Symbolic.moduleBehavior_of_checks` are introduced from flat per-element
facts: a cumulative-start predicate over a *list* of rope pieces is shown
stable under `pairStep` (a `.node` combines adjacent pieces with exactly the
`listLength` start arithmetic the constructors demand), then iterated to the
balanced singleton, with each chunk leaf discharged by list induction. -/

theorem lt_of_getElem?_eq_some {α : Type} {items : List α} {i : Nat} {a : α}
    (h : items[i]? = some a) : i < items.length := by
  cases Nat.lt_or_ge i items.length with
  | inl hlt => exact hlt
  | inr hge =>
      rw [List.getElem?_eq_none_iff.mpr hge] at h
      exact nomatch h

/-! ### Well-formedness (`IndexedRopeWellFormed`) -/

/-- Every rope piece in the list is well-formed at its cumulative start. -/
def indexedRopesWellFormedFrom (program : Program)
    (allWires : Rope (List IndexedWire)) (table : WireTable) :
    Nat → List (Rope (List IndexedWire)) → Prop
  | _, [] => True
  | start, rope :: rest =>
      IndexedRopeWellFormed program allWires table start rope ∧
        indexedRopesWellFormedFrom program allWires table
          (start + rope.listLength) rest

theorem indexedRopesWellFormedFrom_pairStep {program : Program}
    {allWires : Rope (List IndexedWire)} {table : WireTable} :
    ∀ (start : Nat) (ropes : List (Rope (List IndexedWire))),
      indexedRopesWellFormedFrom program allWires table start ropes →
      indexedRopesWellFormedFrom program allWires table start (pairStep ropes)
  | _, [], h => h
  | _, [_], h => h
  | start, one :: two :: rest, h => by
      obtain ⟨h1, h2, hrest⟩ := h
      rw [pairStep_cons_cons]
      refine ⟨.node h1 h2, ?_⟩
      have := indexedRopesWellFormedFrom_pairStep
        (start + one.listLength + two.listLength) rest hrest
      simpa [Rope.listLength, Nat.add_assoc] using this

theorem indexedRopeWellFormed_balancedGo {program : Program}
    {allWires : Rope (List IndexedWire)} {table : WireTable} :
    ∀ (fuel start : Nat) (ropes : List (Rope (List IndexedWire))),
      ropes.length ≤ fuel → ropes ≠ [] →
      indexedRopesWellFormedFrom program allWires table start ropes →
      IndexedRopeWellFormed program allWires table start
        (balancedGo fuel ropes)
  | _, _, [], _, hne, _ => absurd rfl hne
  | fuel, start, [r], _, _, h => by
      have single : balancedGo fuel [r] = r := by cases fuel <;> rfl
      rw [single]
      exact h.1
  | 0, _, _ :: _ :: _, hf, _, _ => by simp at hf
  | fuel + 1, start, x :: y :: t, hf, _, h => by
      show IndexedRopeWellFormed program allWires table start
        (balancedGo fuel (pairStep (x :: y :: t)))
      refine indexedRopeWellFormed_balancedGo fuel start _ ?_ ?_
        (indexedRopesWellFormedFrom_pairStep start _ h)
      · rw [pairStep_length]
        simp only [List.length_cons] at hf ⊢
        omega
      · rw [pairStep_cons_cons]
        exact List.cons_ne_nil _ _

theorem indexedSemanticBlockMatches_of_forall {program : Program}
    {allWires : Rope (List IndexedWire)} {table : WireTable} :
    ∀ (block : List IndexedWire) (start : Nat),
      (∀ (off : Nat) (wire : IndexedWire), block[off]? = some wire →
        indexedWireWellFormedAt program allWires table (start + off) wire =
          true) →
      indexedSemanticBlockMatches program allWires table start block = true
  | [], _, _ => rfl
  | wire :: rest, start, h => by
      simp only [indexedSemanticBlockMatches, Bool.and_eq_true]
      refine ⟨?_, indexedSemanticBlockMatches_of_forall rest (start + 1) ?_⟩
      · simpa using h 0 wire rfl
      · intro off w hw
        have := h (off + 1) w (by simpa using hw)
        simpa [show start + (off + 1) = start + 1 + off by omega] using this

theorem indexedRopesWellFormedFrom_chunks {program : Program}
    {allWires : Rope (List IndexedWire)} {table : WireTable}
    {leafSize : Nat} (positive : 0 < leafSize) :
    ∀ (fuel : Nat) (xs : List IndexedWire), xs.length ≤ fuel →
      ∀ (start : Nat),
      (∀ (off : Nat) (wire : IndexedWire), xs[off]? = some wire →
        indexedWireWellFormedAt program allWires table (start + off) wire =
          true) →
      indexedRopesWellFormedFrom program allWires table start
        ((listChunks leafSize xs).map Rope.leaf)
  | _, [], _, start, _ => by
      rw [listChunks_nil positive, List.map_nil]
      trivial
  | 0, _ :: _, hf, _, _ => by simp at hf
  | fuel + 1, x :: t, hf, start, h => by
      rw [listChunks_cons positive, List.map_cons]
      refine ⟨.leaf (indexedSemanticBlockMatches_of_forall _ start ?_), ?_⟩
      · intro off wire hw
        have hlt : off < ((x :: t).take leafSize).length :=
          lt_of_getElem?_eq_some hw
        rw [List.length_take] at hlt
        refine h off wire ?_
        rw [← List.getElem?_take_of_lt (show off < leafSize by omega)]
        exact hw
      · simp only [Rope.listLength]
        refine indexedRopesWellFormedFrom_chunks positive fuel
          ((x :: t).drop leafSize) ?_
          (start + ((x :: t).take leafSize).length) ?_
        · simp only [List.length_drop, List.length_cons]
          simp only [List.length_cons] at hf
          omega
        · intro off wire hw
          have hx : (x :: t)[leafSize + off]? = some wire := by
            rw [← List.getElem?_drop]
            exact hw
          have hlt : leafSize + off < (x :: t).length :=
            lt_of_getElem?_eq_some hx
          have htake : ((x :: t).take leafSize).length = leafSize := by
            rw [List.length_take]
            omega
          rw [htake,
            show start + leafSize + off = start + (leafSize + off) by omega]
          exact h (leafSize + off) wire hx

/-- Flat per-wire well-formedness lifts to the chunked-and-balanced rope at
any cumulative start. -/
theorem indexedRopeWellFormed_balanced {program : Program}
    {allWires : Rope (List IndexedWire)} {table : WireTable}
    {leafSize : Nat} (positive : 0 < leafSize) (xs : List IndexedWire)
    (start : Nat)
    (h : ∀ (off : Nat) (wire : IndexedWire), xs[off]? = some wire →
      indexedWireWellFormedAt program allWires table (start + off) wire =
        true) :
    IndexedRopeWellFormed program allWires table start
      (balancedRope ((listChunks leafSize xs).map Rope.leaf)) := by
  cases xs with
  | nil =>
      rw [listChunks_nil positive, List.map_nil]
      exact .leaf rfl
  | cons x t =>
      refine indexedRopeWellFormed_balancedGo _ start _ (Nat.le_refl _) ?_
        (indexedRopesWellFormedFrom_chunks positive (x :: t).length (x :: t)
          (Nat.le_refl _) start h)
      rw [listChunks_cons positive, List.map_cons]
      exact List.cons_ne_nil _ _

/-- **Well-formedness introduction for the witness shape.** -/
theorem indexedRopeWellFormed_shaped (program : Program)
    (allWires : Rope (List Loom.Release.Symbolic.IndexedWire))
    (table : Loom.Release.Symbolic.WireTable)
    (k leafSize : Nat) (hs : 0 < leafSize)
    (xs : List Loom.Release.Symbolic.IndexedWire)
    (hwf : ∀ (i : Nat) (wire : Loom.Release.Symbolic.IndexedWire),
      xs[i]? = some wire →
      Loom.Release.Symbolic.indexedWireWellFormedAt program allWires table
        i wire = true) :
    Loom.Release.Symbolic.IndexedRopeWellFormed program allWires table 0
      (balancedRope ((listChunks (2 ^ k)
        ((listChunks leafSize xs).map Rope.leaf)).map balancedRope)) := by
  rw [balancedRope_chunks_pow2]
  exact indexedRopeWellFormed_balanced hs xs 0
    (fun off wire h => by simpa using hwf off wire h)

/-! ### Raw/indexed matching (`IndexedRopeMatches`) -/

/-- Every raw/indexed rope pair in the two lists matches at its cumulative
start. -/
def indexedRopesMatchFrom : Nat → List (Rope (List Wire)) →
    List (Rope (List IndexedWire)) → Prop
  | _, [], [] => True
  | start, raw :: raws, indexed :: indexeds =>
      IndexedRopeMatches start raw indexed ∧
        indexedRopesMatchFrom (start + raw.listLength) raws indexeds
  | _, _, _ => False

theorem indexedRopesMatchFrom_pairStep :
    ∀ (start : Nat) (raws : List (Rope (List Wire)))
      (indexeds : List (Rope (List IndexedWire))),
      indexedRopesMatchFrom start raws indexeds →
      indexedRopesMatchFrom start (pairStep raws) (pairStep indexeds)
  | _, [], [], h => h
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim
  | _, [_], [_], h => h
  | _, [_], _ :: _ :: _, h => (h.2 : False).elim
  | _, _ :: _ :: _, [_], h => (h.2 : False).elim
  | start, r1 :: r2 :: rs, i1 :: i2 :: is, h => by
      obtain ⟨h1, h2, hrest⟩ := h
      rw [pairStep_cons_cons, pairStep_cons_cons]
      refine ⟨.node h1 h2, ?_⟩
      have := indexedRopesMatchFrom_pairStep
        (start + r1.listLength + r2.listLength) rs is hrest
      simpa [Rope.listLength, Nat.add_assoc] using this

theorem indexedRopeMatches_balancedGo :
    ∀ (fuel start : Nat) (raws : List (Rope (List Wire)))
      (indexeds : List (Rope (List IndexedWire))),
      raws.length ≤ fuel → raws ≠ [] → raws.length = indexeds.length →
      indexedRopesMatchFrom start raws indexeds →
      IndexedRopeMatches start (balancedGo fuel raws)
        (balancedGo fuel indexeds)
  | _, _, [], _, _, hne, _, _ => absurd rfl hne
  | fuel, start, [r], [i], _, _, _, h => by
      have er : balancedGo fuel [r] = r := by cases fuel <;> rfl
      have ei : balancedGo fuel [i] = i := by cases fuel <;> rfl
      rw [er, ei]
      exact h.1
  | _, _, [_], [], _, _, hlen, _ => by simp at hlen
  | _, _, [_], _ :: _ :: _, _, _, hlen, _ => by simp at hlen
  | 0, _, _ :: _ :: _, _, hf, _, _, _ => by simp at hf
  | _ + 1, _, _ :: _ :: _, [], _, _, hlen, _ => by simp at hlen
  | _ + 1, _, _ :: _ :: _, [_], _, _, hlen, _ => by simp at hlen
  | fuel + 1, start, r1 :: r2 :: rs, i1 :: i2 :: is, hf, _, hlen, h => by
      show IndexedRopeMatches start
        (balancedGo fuel (pairStep (r1 :: r2 :: rs)))
        (balancedGo fuel (pairStep (i1 :: i2 :: is)))
      refine indexedRopeMatches_balancedGo fuel start _ _ ?_ ?_ ?_
        (indexedRopesMatchFrom_pairStep start _ _ h)
      · rw [pairStep_length]
        simp only [List.length_cons] at hf ⊢
        omega
      · rw [pairStep_cons_cons]
        exact List.cons_ne_nil _ _
      · rw [pairStep_length, pairStep_length]
        simp only [List.length_cons] at hlen ⊢
        omega

theorem indexedRopeMatches_balancedRope (start : Nat)
    (raws : List (Rope (List Wire)))
    (indexeds : List (Rope (List IndexedWire)))
    (hlen : raws.length = indexeds.length)
    (h : indexedRopesMatchFrom start raws indexeds) :
    IndexedRopeMatches start (balancedRope raws) (balancedRope indexeds) := by
  match raws, indexeds with
  | [], [] => exact .leaf rfl
  | [], _ :: _ => simp at hlen
  | _ :: _, [] => simp at hlen
  | r :: rs, i :: is =>
      show IndexedRopeMatches start (balancedGo (r :: rs).length (r :: rs))
        (balancedGo (i :: is).length (i :: is))
      rw [show (i :: is).length = (r :: rs).length from hlen.symm]
      exact indexedRopeMatches_balancedGo (r :: rs).length start (r :: rs)
        (i :: is) (Nat.le_refl _) (List.cons_ne_nil _ _) hlen h

theorem indexedBlockMatches_of_forall :
    ∀ (raws : List Wire) (indexeds : List IndexedWire) (start : Nat),
      raws.length = indexeds.length →
      (∀ (off : Nat) (raw : Wire) (wire : IndexedWire),
        raws[off]? = some raw → indexeds[off]? = some wire →
        wire.matchesRaw (start + off) raw = true) →
      indexedBlockMatches start raws indexeds = true
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | raw :: raws, wire :: indexeds, start, hlen, h => by
      simp only [indexedBlockMatches, Bool.and_eq_true]
      refine ⟨?_, indexedBlockMatches_of_forall raws indexeds (start + 1)
        (by simpa using hlen) ?_⟩
      · simpa using h 0 raw wire rfl rfl
      · intro off r w hr hw
        have := h (off + 1) r w (by simpa using hr) (by simpa using hw)
        simpa [show start + (off + 1) = start + 1 + off by omega] using this

theorem indexedRopesMatchFrom_chunks {leafSize : Nat} (positive : 0 < leafSize) :
    ∀ (fuel : Nat) (raws : List Wire) (indexeds : List IndexedWire),
      raws.length ≤ fuel → raws.length = indexeds.length → ∀ (start : Nat),
      (∀ (off : Nat) (raw : Wire) (wire : IndexedWire),
        raws[off]? = some raw → indexeds[off]? = some wire →
        wire.matchesRaw (start + off) raw = true) →
      indexedRopesMatchFrom start ((listChunks leafSize raws).map Rope.leaf)
        ((listChunks leafSize indexeds).map Rope.leaf)
  | _, [], [], _, _, _, _ => by
      rw [listChunks_nil positive, listChunks_nil positive,
        List.map_nil, List.map_nil]
      trivial
  | _, [], _ :: _, _, hlen, _, _ => by simp at hlen
  | 0, _ :: _, _, hf, _, _, _ => by simp at hf
  | _ + 1, _ :: _, [], _, hlen, _, _ => by simp at hlen
  | fuel + 1, x :: xt, y :: yt, hf, hlen, start, h => by
      rw [listChunks_cons positive, listChunks_cons positive,
        List.map_cons, List.map_cons]
      refine ⟨.leaf (indexedBlockMatches_of_forall _ _ start ?_ ?_), ?_⟩
      · rw [List.length_take, List.length_take, hlen]
      · intro off raw wire hr hw
        have hlt : off < ((x :: xt).take leafSize).length :=
          lt_of_getElem?_eq_some hr
        rw [List.length_take] at hlt
        refine h off raw wire ?_ ?_
        · rw [← List.getElem?_take_of_lt (show off < leafSize by omega)]
          exact hr
        · rw [← List.getElem?_take_of_lt (show off < leafSize by omega)]
          exact hw
      · simp only [Rope.listLength]
        refine indexedRopesMatchFrom_chunks positive fuel
          ((x :: xt).drop leafSize) ((y :: yt).drop leafSize) ?_ ?_
          (start + ((x :: xt).take leafSize).length) ?_
        · simp only [List.length_drop, List.length_cons]
          simp only [List.length_cons] at hf
          omega
        · rw [List.length_drop, List.length_drop, hlen]
        · intro off raw wire hr hw
          have hx : (x :: xt)[leafSize + off]? = some raw := by
            rw [← List.getElem?_drop]
            exact hr
          have hy : (y :: yt)[leafSize + off]? = some wire := by
            rw [← List.getElem?_drop]
            exact hw
          have hlt : leafSize + off < (x :: xt).length :=
            lt_of_getElem?_eq_some hx
          have htake : ((x :: xt).take leafSize).length = leafSize := by
            rw [List.length_take]
            omega
          rw [htake,
            show start + leafSize + off = start + (leafSize + off) by omega]
          exact h (leafSize + off) raw wire hx hy

/-- **Raw/indexed match introduction for two identically shaped ropes.** -/
theorem indexedRopeMatches_shaped (k leafSize : Nat) (hs : 0 < leafSize)
    (raws : List Wire) (indexed : List Loom.Release.Symbolic.IndexedWire)
    (hlen : raws.length = indexed.length)
    (hmatch : ∀ (i : Nat) (raw : Wire)
      (wire : Loom.Release.Symbolic.IndexedWire),
      raws[i]? = some raw → indexed[i]? = some wire →
      wire.matchesRaw i raw = true) :
    Loom.Release.Symbolic.IndexedRopeMatches 0
      (balancedRope ((listChunks (2 ^ k)
        ((listChunks leafSize raws).map Rope.leaf)).map balancedRope))
      (balancedRope ((listChunks (2 ^ k)
        ((listChunks leafSize indexed).map Rope.leaf)).map balancedRope)) := by
  rw [balancedRope_chunks_pow2, balancedRope_chunks_pow2]
  refine indexedRopeMatches_balancedRope 0 _ _ ?_
    (indexedRopesMatchFrom_chunks hs raws.length raws indexed
      (Nat.le_refl _) hlen 0
      (fun off raw wire hr hw => by simpa using hmatch off raw wire hr hw))
  rw [List.length_map, List.length_map, listChunks_length _ hs,
    listChunks_length _ hs, hlen]

end Loom.Release.SSA
