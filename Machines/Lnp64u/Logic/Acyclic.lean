import Machines.Lnp64u.Logic.Wf

/-!
# Lineage acyclicity (L1, the revocation prerequisite)

The `Wf` invariant guarantees every parent pointer reaches a *live*
capability, but not that the parent forest is acyclic. Acyclicity is what
`cap_drop`'s reparent branch needs: splicing a dropped capability's
children onto its parent is only safe when that parent is not itself a
descendant (in particular, not the dropped capability). It is unreachable
by construction — `installDerived` always allocates a *fresh* slot, so a
child's reference never equals an ancestor's — but the bare `Wf` invariant
does not exclude it, so we track it as a companion invariant.

We phrase acyclicity operationally: from any reference, following parent
links terminates at a root (empty parent) within `numLineage` steps. A
cycle would admit an unbounded chain, so this is exactly well-foundedness
of the finite lineage forest. Stated this way the invariant is decidable
per-state and its preservation proofs never need explicit rank arithmetic.
-/

namespace Machines.Lnp64u

open Loom

/-- The parent of the capability referenced by `r` (via its lineage cell),
or `none` if `r` names a root capability or an empty slot. Unlike
`parentOf` this is keyed by a full `CapRef` so parent links compose. -/
def MachineState.parentRef (σ : MachineState) (r : CapRef) : Option CapRef :=
  σ.parentOf r.dom r.slot

/-- Climb `k` parent links from `r`; `none` once a root/empty slot is hit. -/
def MachineState.climb (σ : MachineState) : Nat → CapRef → Option CapRef
  | 0,     r => some r
  | k + 1, r => (σ.parentRef r).bind (σ.climb k)

/-- The maximum length of an acyclic parent chain: distinct references use
distinct lineage cells (`ptr_inj`), and there are `numDomains × numLineage`
cells in all — chains cross domains (e.g. `mem_grant` derives into another
domain), so the bound is the *total* cell count, not one domain's. -/
def chainBound : Nat := numDomains * numLineage

/-- **Lineage acyclicity.** No reference is a proper ancestor of itself: the
parent chain from `r` never returns to `r`. This is genuine acyclicity of the
lineage forest — the companion invariant `cap_drop`/`cap_revoke`/the gate ops
need. Stated as no-return-to-start, its preservation proofs never need cell
counting: every kernel op is edge-removal, edge-contraction, or fresh-leaf
addition, none of which can create a cycle. -/
def Acyclic (σ : MachineState) : Prop :=
  ∀ (r : CapRef) (i : Nat), 0 < i → σ.climb i r ≠ some r

/-- Climbing past a root stays `none`. -/
@[simp] theorem MachineState.climb_none (σ : MachineState) (k : Nat) :
    ∀ (r : CapRef), σ.parentRef r = none → σ.climb (k + 1) r = none := by
  intro r hr; unfold MachineState.climb; rw [hr]; rfl

/-- If a state has *no* occupied lineage cells, every parent link is empty,
so it is trivially acyclic. Covers the boot state. -/
theorem acyclic_of_no_lineage (σ : MachineState)
    (h : ∀ d l, (σ.doms d).lineage l = none) : Acyclic σ := by
  have hpar : ∀ r, σ.parentRef r = none := by
    intro r; unfold MachineState.parentRef MachineState.parentOf
    cases hc : (σ.doms r.dom).caps r.slot with
    | none => simp
    | some e =>
        cases hle : e.lineage with
        | none => simp [hle]
        | some l => simp [hle, h r.dom l]
  intro r i hi
  cases hik : i with
  | zero => omega
  | succ k => rw [σ.climb_none k r (hpar r)]; simp

/-- **Boot acyclicity.** The reset state's lineage tables are empty. -/
theorem init_acyclic (m : Manifest) : Acyclic (m.initState) :=
  acyclic_of_no_lineage _ (fun _ _ => rfl)

/-- A self-parenting reference climbs to itself forever. -/
theorem MachineState.climb_self (σ : MachineState) (r : CapRef)
    (h : σ.parentRef r = some r) : ∀ k, σ.climb k r = some r := by
  intro k; induction k with
  | zero => rfl
  | succ n ih => unfold MachineState.climb; rw [h]; simpa using ih

/-- **No self-parenting.** Under acyclicity, no capability is its own
parent — the fact `cap_drop`'s reparent branch turns on. -/
theorem Acyclic.parentRef_ne (σ : MachineState) (hac : Acyclic σ)
    (r p : CapRef) (h : σ.parentRef r = some p) : p ≠ r := by
  rintro rfl
  exact hac p 1 (by omega) (by unfold MachineState.climb; rw [h]; rfl)

/-- Climbing depends only on the parent function: two states with the same
parent links agree on every climb. -/
theorem MachineState.climb_congr (σ σ' : MachineState)
    (hpar : ∀ r, σ'.parentRef r = σ.parentRef r) :
    ∀ k r, σ'.climb k r = σ.climb k r := by
  intro k; induction k with
  | zero => intro r; rfl
  | succ n ih =>
      intro r; unfold MachineState.climb; rw [hpar r]
      cases σ.parentRef r with
      | none => rfl
      | some p => simpa using ih p

/-- **Acyclicity transports along equal parent structure.** Any operation
that leaves every parent link unchanged (all non-lineage-touching ops:
register writes, PC updates, scheduling, region installs, Mover programming,
gate bookkeeping) preserves acyclicity for free. -/
theorem acyclic_of_parentRef_eq (σ σ' : MachineState)
    (hpar : ∀ r, σ'.parentRef r = σ.parentRef r) (hac : Acyclic σ) : Acyclic σ' := by
  intro r i hi; rw [σ.climb_congr σ' hpar i r]; exact hac r i hi

/-- Parent links are determined by each domain's `caps` and `lineage`
tables; an operation preserving both preserves every parent link. -/
theorem parentRef_eq_of_doms (σ σ' : MachineState)
    (hd : ∀ d, (σ'.doms d).caps = (σ.doms d).caps ∧
               (σ'.doms d).lineage = (σ.doms d).lineage) :
    ∀ r, σ'.parentRef r = σ.parentRef r := by
  intro r; unfold MachineState.parentRef MachineState.parentOf
  rw [(hd r.dom).1, (hd r.dom).2]

/-- If an operation only *removes* parent links (each link is either
unchanged or dropped to `none`), then any chain that terminated still
terminates. Covers `clearSlot`, `orphanChildren`, and the sweeps — every
edge-removing revocation step. -/
theorem MachineState.climb_none_mono (σ σ' : MachineState)
    (hpar : ∀ r, σ'.parentRef r = σ.parentRef r ∨ σ'.parentRef r = none) :
    ∀ k r, σ.climb k r = none → σ'.climb k r = none := by
  intro k; induction k with
  | zero => intro r h; simp [MachineState.climb] at h
  | succ n ih =>
      intro r h
      unfold MachineState.climb
      rcases hpar r with he | he
      · rw [he]
        rw [MachineState.climb] at h
        cases hp : σ.parentRef r with
        | none => rfl
        | some p => rw [hp] at h; simp only [Option.bind_some] at h ⊢; exact ih p h
      · rw [he]; rfl

/-- Under edge removal, any surviving (`some`) climb equals the original: each
step that stayed `some` used the unchanged parent link. -/
theorem MachineState.climb_le_eq (σ σ' : MachineState)
    (hpar : ∀ r, σ'.parentRef r = σ.parentRef r ∨ σ'.parentRef r = none) :
    ∀ k r x, σ'.climb k r = some x → σ.climb k r = some x := by
  intro k; induction k with
  | zero => intro r x h; simpa [MachineState.climb] using h
  | succ n ih =>
      intro r x h
      rw [MachineState.climb] at h ⊢
      rcases hpar r with he | he
      · rw [he] at h
        cases hp : σ.parentRef r with
        | none => rw [hp] at h; simp at h
        | some p => rw [hp] at h; simp only [Option.bind_some] at h ⊢; exact ih p x h
      · rw [he] at h; simp at h

/-- **Acyclicity survives edge removal.** An operation that only drops
parent links preserves acyclicity: a cycle would survive back into `σ`. -/
theorem acyclic_of_parentRef_le (σ σ' : MachineState)
    (hpar : ∀ r, σ'.parentRef r = σ.parentRef r ∨ σ'.parentRef r = none)
    (hac : Acyclic σ) : Acyclic σ' :=
  fun r i hi hcyc => hac r i hi (σ.climb_le_eq σ' hpar i r r hcyc)

/-- Climbs compose: `a + b` links is `a` links then `b` more. -/
theorem MachineState.climb_add (σ : MachineState) (b : Nat) :
    ∀ (a : Nat) (r : CapRef), σ.climb (a + b) r = (σ.climb a r).bind (σ.climb b) := by
  intro a; induction a with
  | zero => intro r; simp [MachineState.climb]
  | succ n ih =>
      intro r
      show σ.climb (n + 1 + b) r = _
      have : n + 1 + b = (n + b) + 1 := by omega
      rw [this]
      rw [show σ.climb ((n + b) + 1) r = (σ.parentRef r).bind (σ.climb (n + b)) from by
        cases hp : σ.parentRef r with
        | none => simp [MachineState.climb, hp]
        | some p => simp [MachineState.climb, hp]]
      rw [show σ.climb (n + 1) r = (σ.parentRef r).bind (σ.climb n) from by
        cases hp : σ.parentRef r with
        | none => simp [MachineState.climb, hp]
        | some p => simp [MachineState.climb, hp]]
      cases hp : σ.parentRef r with
      | none => simp
      | some p => simp only [hp, Option.bind_some]; exact ih p

/-- Once a chain dies it stays dead as the horizon grows. -/
theorem MachineState.climb_mono_none (σ : MachineState) :
    ∀ k r, σ.climb k r = none → σ.climb (k + 1) r = none := by
  intro k; induction k with
  | zero => intro r h; simp [MachineState.climb] at h
  | succ n ih =>
      intro r h
      rw [show σ.climb (n + 1) r = (σ.parentRef r).bind (σ.climb n) from by
        cases hp : σ.parentRef r with
        | none => simp [MachineState.climb, hp]
        | some p => simp [MachineState.climb, hp]] at h
      rw [show σ.climb (n + 1 + 1) r = (σ.parentRef r).bind (σ.climb (n + 1)) from by
        cases hp : σ.parentRef r with
        | none => simp [MachineState.climb, hp]
        | some p => simp [MachineState.climb, hp]]
      cases hp : σ.parentRef r with
      | none => simp
      | some p => simp only [hp, Option.bind_some] at h ⊢; exact ih p h

/-- A dead chain stays dead at every larger horizon. -/
theorem MachineState.climb_none_ge (σ : MachineState) (k : Nat) (r : CapRef)
    (h : σ.climb k r = none) : ∀ m, k ≤ m → σ.climb m r = none := by
  intro m
  induction m with
  | zero => intro hm; have hk : k = 0 := Nat.le_zero.mp hm; subst hk; exact h
  | succ n ih =>
      intro hm
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact σ.climb_mono_none n r (ih (by omega))
      · have hk : k = n + 1 := by omega
        rw [← hk]; exact h

/-- **Acyclicity survives edge contraction.** If an operation reroutes every
link into `a` onto `a`'s own parent `b` (splicing `a` out) and leaves all
other links unchanged, acyclicity is preserved: each rerouted chain is the
original with `a` skipped, hence no longer. This is exactly what `reparent`
does in `cap_drop` (`a` = dropped ref, `b` = its parent). -/
theorem acyclic_contract (σ σ' : MachineState) (a b : CapRef)
    (hab : σ.parentRef a = some b)
    (hpar : ∀ r, σ'.parentRef r =
      if σ.parentRef r = some a then some b else σ.parentRef r)
    (hac : Acyclic σ) : Acyclic σ' := by
  have hc1 : ∀ x, σ.climb 1 x = σ.parentRef x := by intro x; simp [MachineState.climb]
  have hkey : ∀ k r, ∃ m, k ≤ m ∧ σ'.climb k r = σ.climb m r := by
    intro k; induction k with
    | zero => intro r; exact ⟨0, le_refl _, rfl⟩
    | succ n ih =>
        intro r
        have hstep : σ'.climb (n + 1) r = (σ'.parentRef r).bind (σ'.climb n) := by
          cases hp : σ'.parentRef r with
          | none => simp [MachineState.climb, hp]
          | some p => simp [MachineState.climb, hp]
        rw [hstep, hpar r]
        by_cases hra : σ.parentRef r = some a
        · rw [if_pos hra]; simp only [Option.bind_some]
          obtain ⟨m, hm, he⟩ := ih b
          refine ⟨2 + m, by omega, ?_⟩
          rw [he, σ.climb_add m 2 r]
          have h2 : σ.climb 2 r = some b := by
            show σ.climb (1 + 1) r = some b
            rw [σ.climb_add 1 1 r, hc1 r, hra, Option.bind_some, hc1 a, hab]
          rw [h2]; simp
        · rw [if_neg hra]
          cases hq : σ.parentRef r with
          | none =>
              refine ⟨n + 1, le_refl _, ?_⟩
              simp only [Option.bind_none]
              have : σ.climb (n + 1) r = none := by rw [σ.climb_none n r hq]
              rw [this]
          | some q =>
              simp only [Option.bind_some]
              obtain ⟨m, hm, he⟩ := ih q
              refine ⟨1 + m, by omega, ?_⟩
              rw [he, σ.climb_add m 1 r, hc1 r, hq, Option.bind_some]
  
  intro r i hi hcyc
  obtain ⟨m, hm, he⟩ := hkey i r
  rw [hcyc] at he
  exact hac r m (by omega) he.symm



/-- Any `setDom` whose update preserves the domain's `caps` and `lineage`
tables preserves acyclicity — covers every register/PC/region/budget/schedule
update (all the non-lineage `setDom` operations). -/
theorem acyclic_setDom (σ : MachineState) (d' : DomainId) (f : DomainState → DomainState)
    (hf : ∀ ds, (f ds).caps = ds.caps ∧ (f ds).lineage = ds.lineage) (hac : Acyclic σ) :
    Acyclic (σ.setDom d' f) := by
  refine acyclic_of_parentRef_eq σ _ (parentRef_eq_of_doms σ _ (fun d => ?_)) hac
  by_cases h : d = d'
  · subst h
    simp only [MachineState.setDom, Loom.Fun.update_same, (hf (σ.doms d)).1, (hf (σ.doms d)).2,
      and_self]
  · simp only [MachineState.setDom, Loom.Fun.update_ne _ _ _ _ h, and_self]

/-- Writing memory preserves acyclicity (it touches only `mem`). -/
theorem acyclic_write (σ : MachineState) (a : Addr) (v : Loom.Word32) (hac : Acyclic σ) :
    Acyclic (σ.write a v) :=
  acyclic_of_parentRef_eq σ _ (parentRef_eq_of_doms σ _ (fun _ => ⟨rfl, rfl⟩)) hac


/-- **Acyclicity survives fresh-leaf addition.** Adding a single parent link
`a → b` where `a` was a root (nothing pointed to `a`, and `a ≠ b`) cannot
create a cycle: a cycle would have to re-enter `a`, but nothing points to it.
This is exactly `installDerived` (a new capability in a free slot). No counting. -/
theorem acyclic_add_leaf (σ σ' : MachineState) (a b : CapRef) (hne : a ≠ b)
    (hpar : ∀ r, σ'.parentRef r = if r = a then some b else σ.parentRef r)
    (hno : ∀ r, σ.parentRef r ≠ some a) (hac : Acyclic σ) : Acyclic σ' := by
  have hno' : ∀ r, σ'.parentRef r ≠ some a := by
    intro r; rw [hpar]; split
    · intro h; exact hne (Option.some.inj h).symm
    · exact hno r
  have havoid : ∀ k r, r ≠ a → σ'.climb k r ≠ some a := by
    intro k; induction k with
    | zero => intro r hr h; simp only [MachineState.climb, Option.some.injEq] at h; exact hr h
    | succ n ih =>
        intro r hr h; rw [MachineState.climb] at h
        cases hp : σ'.parentRef r with
        | none => rw [hp] at h; simp at h
        | some p =>
            rw [hp] at h; simp only [Option.bind_some] at h
            exact ih p (fun hpe => hno' r (by rw [hp, hpe])) h
  have heq : ∀ k r, r ≠ a → σ'.climb k r = σ.climb k r := by
    intro k; induction k with
    | zero => intro r hr; rfl
    | succ n ih =>
        intro r hr
        rw [MachineState.climb, MachineState.climb, hpar, if_neg hr]
        cases hp : σ.parentRef r with
        | none => rfl
        | some p =>
            simp only [Option.bind_some]
            exact ih p (fun hpe => hno r (by rw [hp, hpe]))
  intro r i hi hcyc
  by_cases hra : r = a
  · cases hik : i with
    | zero => omega
    | succ i' =>
        have hstep : σ'.climb (i' + 1) r = (σ'.parentRef r).bind (σ'.climb i') := by
          cases hp : σ'.parentRef r with
          | none => simp [MachineState.climb, hp]
          | some p => simp [MachineState.climb, hp]
        rw [hik, hstep, hpar, if_pos hra] at hcyc
        simp only [Option.bind_some] at hcyc
        rw [hra] at hcyc
        exact havoid i' b (fun h => hne h.symm) hcyc
  · rw [heq i r hra] at hcyc; exact hac r i hi hcyc

end Machines.Lnp64u
