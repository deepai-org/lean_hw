-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Footprint
import Loom.Hw.ReadsOk

/-!
# Frame rules (PLATONIC W2)

`Footprint.lean` has the *write* side: an action that does not write `(rn, w)`
leaves that entry alone. That bounds what a rule can disturb.

Missing was the *read* side, which is the half that makes proof cost scale with
a property's dependency cone: **an expression cannot see state outside its own
footprint.** With both halves, a property about register `X` needs only the
rules that write `X`, evaluated against only the state those rules read — the
rest of the design is framed out instead of being carried through the proof.

The footprint is `Expr.readSites` from W1.1 (`ReadsOk.lean`), so the same
syntactic analysis that gates emission is the one the proofs quantify over;
there is no second notion of "what this expression depends on" to keep in sync.

Memories are approximated by *name and data width*, not by address: an
expression's address operand is dynamic, so `readSites` cannot name the cell.
`AgreeOn` therefore demands agreement at every address of a read memory. That
is sound and is what a syntactic footprint can honestly promise; a sharper
address-level footprint would need the address to be a proven-constant, which
is a separate (and much more specialised) analysis.
-/

namespace Loom.Hw

/-- Two states agree on a footprint: on the listed register entries, and at
*every* address of the listed memories (see the note above on why memories are
name-and-width rather than address-precise). -/
def St.AgreeOn (rs ms : List (String × Nat)) (σ τ : St) : Prop :=
  (∀ n w, (n, w) ∈ rs → σ.regs n w = τ.regs n w) ∧
  (∀ m w, (m, w) ∈ ms → ∀ a, σ.mems m a w = τ.mems m a w)

theorem St.AgreeOn.mono {rs ms rs' ms' : List (String × Nat)} {σ τ : St}
    (hr : ∀ x, x ∈ rs' → x ∈ rs) (hm : ∀ x, x ∈ ms' → x ∈ ms)
    (h : St.AgreeOn rs ms σ τ) : St.AgreeOn rs' ms' σ τ :=
  ⟨fun n w hn => h.1 n w (hr _ hn), fun m w hmw => h.2 m w (hm _ hmw)⟩

theorem St.AgreeOn.append_left {rs ms rs' ms' : List (String × Nat)} {σ τ : St}
    (h : St.AgreeOn (rs ++ rs') (ms ++ ms') σ τ) : St.AgreeOn rs ms σ τ :=
  h.mono (fun _ hx => List.mem_append.mpr (Or.inl hx))
         (fun _ hx => List.mem_append.mpr (Or.inl hx))

theorem St.AgreeOn.append_right {rs ms rs' ms' : List (String × Nat)} {σ τ : St}
    (h : St.AgreeOn (rs ++ rs') (ms ++ ms') σ τ) : St.AgreeOn rs' ms' σ τ :=
  h.mono (fun _ hx => List.mem_append.mpr (Or.inr hx))
         (fun _ hx => List.mem_append.mpr (Or.inr hx))

theorem St.AgreeOn.trans {rs ms : List (String × Nat)} {σ τ υ : St}
    (hστ : St.AgreeOn rs ms σ τ) (hτυ : St.AgreeOn rs ms τ υ) :
    St.AgreeOn rs ms σ υ :=
  ⟨fun n w selected => (hστ.1 n w selected).trans (hτυ.1 n w selected),
   fun m w selected addr =>
    (hστ.2 m w selected addr).trans (hτυ.2 m w selected addr)⟩

theorem St.AgreeOn.refl {rs ms : List (String × Nat)} {σ : St} :
    St.AgreeOn rs ms σ σ :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem St.AgreeOn.symm {rs ms : List (String × Nat)} {σ τ : St}
    (h : St.AgreeOn rs ms σ τ) : St.AgreeOn rs ms τ σ :=
  ⟨fun n w selected => (h.1 n w selected).symm,
   fun m w selected addr => (h.2 m w selected addr).symm⟩

/-- **The frame rule for expressions.** An expression evaluates identically in
any two states that agree on its footprint. Everything outside `readSites` is
irrelevant to its value — which is exactly the licence to ignore the rest of
the design when proving a property about it. -/
theorem Expr.eval_congr_of_agree : ∀ {w : Nat} (e : Expr w) {σ τ : St},
    St.AgreeOn e.readSites.1 e.readSites.2 σ τ → e.eval σ = e.eval τ := by
  intro w e
  induction e with
  | lit v => intro _ _ _; rfl
  | reg w n => intro σ τ h; exact h.1 n w (by simp [Expr.readSites])
  | memRead dw m a ih =>
      intro σ τ h
      have hm : (m, dw) ∈ ((m, dw) :: a.readSites.2) := by simp
      have ha : St.AgreeOn a.readSites.1 a.readSites.2 σ τ :=
        ⟨fun n w hn => h.1 n w (by simpa [Expr.readSites] using hn),
         fun m' w' hm' => h.2 m' w' (by
           simp only [Expr.readSites]
           exact List.mem_cons_of_mem _ hm')⟩
      show σ.mems m (a.eval σ).toNat dw = τ.mems m (a.eval τ).toNat dw
      rw [ih ha]
      exact h.2 m dw (by simp [Expr.readSites]) _
  | not a ih => intro σ τ h; simp [Expr.eval, ih (by simp [Expr.readSites] at h ⊢; exact h)]
  | slice a lo width ih =>
      intro σ τ h; simp [Expr.eval, ih (by simpa [Expr.readSites] using h)]
  | zext a w' ih => intro σ τ h; simp [Expr.eval, ih (by simpa [Expr.readSites] using h)]
  | sext a w' ih => intro σ τ h; simp [Expr.eval, ih (by simpa [Expr.readSites] using h)]
  | mux c t f ihc iht ihf =>
      intro σ τ h
      simp only [Expr.readSites] at h
      -- footprint is c ++ t ++ f on both components
      -- `r ++ r' ++ r''` associates to the LEFT: `(c ++ t) ++ f`.
      have hct := h.append_left
      have hf : St.AgreeOn f.readSites.1 f.readSites.2 σ τ := h.append_right
      have hc : St.AgreeOn c.readSites.1 c.readSites.2 σ τ := hct.append_left
      have ht : St.AgreeOn t.readSites.1 t.readSites.2 σ τ := hct.append_right
      simp [Expr.eval, ihc hc, iht ht, ihf hf]
  | and a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | or a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | xor a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | add a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | sub a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | shl a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | shr a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | eq a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | ult a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]
  | slt a b iha ihb =>
      intro σ τ h; simp only [Expr.readSites] at h
      simp [Expr.eval, iha h.append_left, ihb h.append_right]

/-- **The frame rule for a cycle.** A register no rule of the design writes is
carried through `Design.cycle` unchanged.

This is the lift of `Act.run_regs_notin` from one action to a whole cycle, and
it is what lets a proof about one register ignore every rule that does not
mention it — the dependency-cone property W2 is after. -/
theorem Design.cycle_regs_notin (d : Design) (rn : String) (w : Nat)
    (h : ∀ r ∈ d.rules, (rn, w) ∉ r.body.regWrites) (σ : St) :
    (d.cycle σ).regs rn w = σ.regs rn w := by
  show (d.rules.foldl (fun acc r => r.body.run σ acc) σ).regs rn w = σ.regs rn w
  -- generalise the accumulator so the fold can be inducted on
  suffices H : ∀ (rs : List Rule) (acc : St),
      (∀ r ∈ rs, (rn, w) ∉ r.body.regWrites) →
      (rs.foldl (fun acc r => r.body.run σ acc) acc).regs rn w = acc.regs rn w by
    exact H d.rules σ h
  intro rs
  induction rs with
  | nil => intro acc _; rfl
  | cons r rest ih =>
      intro acc hmem
      have hr : (rn, w) ∉ r.body.regWrites := hmem r (List.mem_cons_self)
      have hrest : ∀ r' ∈ rest, (rn, w) ∉ r'.body.regWrites :=
        fun r' hr' => hmem r' (List.mem_cons_of_mem _ hr')
      show (rest.foldl (fun acc r => r.body.run σ acc) (r.body.run σ acc)).regs rn w
             = acc.regs rn w
      rw [ih _ hrest, Act.run_regs_notin rn w r.body hr]

/-- Likewise for memories: a memory no rule writes survives a cycle, at every
address and width. Stated pointwise to match `Act.run_mems_notin`. -/
theorem Design.cycle_mems_notin (d : Design) (mn : String)
    (h : ∀ r ∈ d.rules, mn ∉ r.body.memWrites) (σ : St) (ad w : Nat) :
    (d.cycle σ).mems mn ad w = σ.mems mn ad w := by
  show (d.rules.foldl (fun acc r => r.body.run σ acc) σ).mems mn ad w = σ.mems mn ad w
  suffices H : ∀ (rs : List Rule) (acc : St),
      (∀ r ∈ rs, mn ∉ r.body.memWrites) →
      (rs.foldl (fun acc r => r.body.run σ acc) acc).mems mn ad w = acc.mems mn ad w by
    exact H d.rules σ h
  intro rs
  induction rs with
  | nil => intro acc _; rfl
  | cons r rest ih =>
      intro acc hmem
      have hr : mn ∉ r.body.memWrites := hmem r (List.mem_cons_self)
      have hrest : ∀ r' ∈ rest, mn ∉ r'.body.memWrites :=
        fun r' hr' => hmem r' (List.mem_cons_of_mem _ hr')
      show (rest.foldl (fun acc r => r.body.run σ acc) (r.body.run σ acc)).mems mn ad w
             = acc.mems mn ad w
      rw [ih _ hrest, Act.run_mems_notin mn r.body hr]

/-! ## Property-directed cycle projection

The all-or-nothing frame lemmas above prove that an entirely unwritten
coordinate is unchanged.  For a coordinate that *is* written, proofs should
still inspect only its writers.  Because every expression reads the fixed
pre-cycle state, deleting rules that do not write the projected coordinate
cannot affect that coordinate's result.
-/

/-- Since action expressions read only the pre-cycle state, agreement of one
accumulator register is preserved through any action. -/
theorem Act.run_regs_congr_acc (a : Act) (σ acc₁ acc₂ : St)
    (rn : String) (w : Nat) (h : acc₁.regs rn w = acc₂.regs rn w) :
    (a.run σ acc₁).regs rn w = (a.run σ acc₂).regs rn w := by
  induction a generalizing acc₁ acc₂ with
  | skip => exact h
  | seq a b iha ihb => exact ihb _ _ (iha _ _ h)
  | ite c t e iht ihe =>
      by_cases hc : c.eval σ = 1#1
      · simp [Act.run, hc, iht _ _ h]
      · simp [Act.run, hc, ihe _ _ h]
  | write w' rn' v =>
      simp only [Act.run, RegEnv.set]
      by_cases hr : rn = rn'
      · subst rn
        simp only [if_pos]
        by_cases hw : w' = w
        · subst w; simp
        · simp [hw, h]
      · simp [hr, h]
  | memWrite => exact h

/-! ### Intra-rule projection

Rule-level support removes unrelated rules, but one retained rule can still be
large.  `projectRegs` removes writes outside a selected register footprint and
collapses the no-op action structure left behind.  Since all expressions read
the fixed pre-cycle state, this changes none of the selected accumulator
coordinates.
-/

/-- Sequence constructor that erases syntactic no-ops. -/
def Act.smartSeq : Act → Act → Act
  | .skip, right => right
  | left, .skip => left
  | left, right => .seq left right

/-- Conditional constructor that erases a branch with two no-op arms. -/
def Act.smartIte (guard : Expr 1) : Act → Act → Act
  | .skip, .skip => .skip
  | thenAction, elseAction => .ite guard thenAction elseAction

@[simp] theorem Act.smartSeq_run (left right : Act) (σ acc : St) :
    (left.smartSeq right).run σ acc = (Act.seq left right).run σ acc := by
  cases left <;> cases right <;> rfl

theorem Act.smartIte_run (guard : Expr 1) (thenAction elseAction : Act)
    (σ acc : St) :
    (smartIte guard thenAction elseAction).run σ acc =
      (Act.ite guard thenAction elseAction).run σ acc := by
  cases thenAction <;> cases elseAction <;> simp [smartIte, Act.run]

/-- Retain only writes to selected register coordinates. Memory writes and
unselected register writes become no-ops; guards are retained exactly when a
selected write remains below them. -/
def Act.projectRegs (coords : List (String × Nat)) : Act → Act
  | .skip => .skip
  | .seq left right =>
      smartSeq (left.projectRegs coords) (right.projectRegs coords)
  | .ite guard thenAction elseAction =>
      smartIte guard (thenAction.projectRegs coords)
        (elseAction.projectRegs coords)
  | .write width name value =>
      if coords.contains (name, width) then .write width name value else .skip
  | .memWrite .. => .skip

/-- Projecting an action preserves every selected register coordinate. -/
theorem Act.projectRegs_run (coords : List (String × Nat))
    (name : String) (width : Nat) (selected : (name, width) ∈ coords) :
    ∀ (action : Act) (σ acc : St),
      ((action.projectRegs coords).run σ acc).regs name width =
        (action.run σ acc).regs name width := by
  intro action
  induction action with
  | skip => intro σ acc; rfl
  | seq left right ihLeft ihRight =>
      intro σ acc
      simp only [projectRegs]
      rw [smartSeq_run]
      exact ihRight σ _ |>.trans
        (right.run_regs_congr_acc σ _ _ name width (ihLeft σ acc))
  | ite guard thenAction elseAction ihThen ihElse =>
      intro σ acc
      simp only [projectRegs]
      rw [smartIte_run]
      by_cases hguard : guard.eval σ = 1#1
      · simp [Act.run, hguard, ihThen σ acc]
      · simp [Act.run, hguard, ihElse σ acc]
  | write actualWidth actualName value =>
      intro σ acc
      by_cases kept : (actualName, actualWidth) ∈ coords
      · simp [projectRegs, kept]
      · simp only [projectRegs, List.contains_eq_mem, kept, decide_false,
          Bool.false_eq_true, ↓reduceIte, Act.run]
        exact (Act.run_regs_notin name width (.write actualWidth actualName value)
          (by
            intro written
            have same : (name, width) = (actualName, actualWidth) := by
              simpa [Act.regWrites] using written
            exact kept (same ▸ selected)) σ acc).symm
  | memWrite => intro σ acc; rfl

/-- Retain only writes to selected memory name/data-width coordinates.
Register writes and unselected memory writes become no-ops. Addresses remain
dynamic: selecting a memory coordinate preserves every address in that bank. -/
def Act.projectMems (coords : List (String × Nat)) : Act → Act
  | .skip => .skip
  | .seq left right =>
      smartSeq (left.projectMems coords) (right.projectMems coords)
  | .ite guard thenAction elseAction =>
      smartIte guard (thenAction.projectMems coords)
        (elseAction.projectMems coords)
  | .write .. => .skip
  | .memWrite addrWidth dataWidth name port addr value =>
      if coords.contains (name, dataWidth) then
        .memWrite addrWidth dataWidth name port addr value
      else .skip

/-- Memory-entry analogue of `Act.run_regs_congr_acc`. -/
theorem Act.run_mems_congr_acc (act : Act) (σ acc₁ acc₂ : St)
    (mn : String) (addr width : Nat)
    (h : acc₁.mems mn addr width = acc₂.mems mn addr width) :
    (act.run σ acc₁).mems mn addr width =
      (act.run σ acc₂).mems mn addr width := by
  induction act generalizing acc₁ acc₂ with
  | skip => exact h
  | seq a b iha ihb => exact ihb _ _ (iha _ _ h)
  | ite c t e iht ihe =>
      by_cases hc : c.eval σ = 1#1
      · simp [Act.run, hc, iht _ _ h]
      · simp [Act.run, hc, ihe _ _ h]
  | write => exact h
  | memWrite aw dw mem port writeAddr data =>
      simp only [Act.run, MemEnv.set]
      by_cases hma : mn = mem ∧ addr = (writeAddr.eval σ).toNat
      · rw [if_pos hma, if_pos hma]
        by_cases hw : dw = width
        · rw [dif_pos hw, dif_pos hw]
        · rw [dif_neg hw, dif_neg hw]; exact h
      · rw [if_neg hma, if_neg hma]; exact h

/-- Projecting an action preserves every address of every selected memory
name/data-width coordinate. -/
theorem Act.projectMems_run (coords : List (String × Nat))
    (name : String) (width : Nat) (selected : (name, width) ∈ coords) :
    ∀ (action : Act) (σ acc : St) (addr : Nat),
      ((action.projectMems coords).run σ acc).mems name addr width =
        (action.run σ acc).mems name addr width := by
  intro action
  induction action with
  | skip => intro σ acc addr; rfl
  | seq left right ihLeft ihRight =>
      intro σ acc addr
      simp only [projectMems]
      rw [smartSeq_run]
      exact ihRight σ _ addr |>.trans
        (right.run_mems_congr_acc σ _ _ name addr width (ihLeft σ acc addr))
  | ite guard thenAction elseAction ihThen ihElse =>
      intro σ acc addr
      simp only [projectMems]
      rw [smartIte_run]
      by_cases hguard : guard.eval σ = 1#1
      · simp [Act.run, hguard, ihThen σ acc addr]
      · simp [Act.run, hguard, ihElse σ acc addr]
  | write => intro σ acc addr; rfl
  | memWrite addrWidth dataWidth actualName port writeAddr value =>
      intro σ acc addr
      by_cases kept : (actualName, dataWidth) ∈ coords
      · simp [projectMems, kept]
      · simp only [projectMems, List.contains_eq_mem, kept, decide_false,
          Bool.false_eq_true, ↓reduceIte, Act.run]
        symm
        simp only [MemEnv.set]
        by_cases hit : name = actualName ∧ addr = (writeAddr.eval σ).toNat
        · rw [if_pos hit]
          have widthNe : dataWidth ≠ width := by
            intro sameWidth
            exact kept (by simpa [hit.1, sameWidth] using selected)
          rw [dif_neg widthNe]
        · rw [if_neg hit]

/-- A register-only projection has no memory effect. -/
theorem Act.projectRegs_run_mems (coords : List (String × Nat))
    (action : Act) (σ acc : St) (name : String) (addr width : Nat) :
    ((action.projectRegs coords).run σ acc).mems name addr width =
      acc.mems name addr width := by
  induction action generalizing acc with
  | skip => rfl
  | seq left right ihLeft ihRight =>
      simp only [projectRegs]
      rw [smartSeq_run]
      simp only [Act.run]
      rw [ihRight, ihLeft]
  | ite guard thenAction elseAction ihThen ihElse =>
      simp only [projectRegs]
      rw [smartIte_run]
      by_cases hguard : guard.eval σ = 1#1
      · simp [Act.run, hguard, ihThen]
      · simp [Act.run, hguard, ihElse]
  | write actualWidth actualName value =>
      by_cases kept : (actualName, actualWidth) ∈ coords <;>
        simp [projectRegs, kept, Act.run]
  | memWrite => rfl

/-- A memory-only projection has no register effect. -/
theorem Act.projectMems_run_regs (coords : List (String × Nat))
    (action : Act) (σ acc : St) (name : String) (width : Nat) :
    ((action.projectMems coords).run σ acc).regs name width =
      acc.regs name width := by
  induction action generalizing acc with
  | skip => rfl
  | seq left right ihLeft ihRight =>
      simp only [projectMems]
      rw [smartSeq_run]
      simp only [Act.run]
      rw [ihRight, ihLeft]
  | ite guard thenAction elseAction ihThen ihElse =>
      simp only [projectMems]
      rw [smartIte_run]
      by_cases hguard : guard.eval σ = 1#1
      · simp [Act.run, hguard, ihThen]
      · simp [Act.run, hguard, ihElse]
  | write => rfl
  | memWrite addrWidth dataWidth actualName port writeAddr value =>
      by_cases kept : (actualName, dataWidth) ∈ coords <;>
        simp [projectMems, kept, Act.run]

private theorem rulesFold_regs_congr_acc (rules : List Rule) (σ acc₁ acc₂ : St)
    (rn : String) (w : Nat) (h : acc₁.regs rn w = acc₂.regs rn w) :
    (rules.foldl (fun acc rule => rule.body.run σ acc) acc₁).regs rn w =
      (rules.foldl (fun acc rule => rule.body.run σ acc) acc₂).regs rn w := by
  induction rules generalizing acc₁ acc₂ with
  | nil => exact h
  | cons rule rest ih =>
      exact ih _ _ (rule.body.run_regs_congr_acc σ acc₁ acc₂ rn w h)

private theorem rulesFold_mems_congr_acc (rules : List Rule) (σ acc₁ acc₂ : St)
    (mn : String) (addr width : Nat)
    (h : acc₁.mems mn addr width = acc₂.mems mn addr width) :
    (rules.foldl (fun acc rule => rule.body.run σ acc) acc₁).mems mn addr width =
      (rules.foldl (fun acc rule => rule.body.run σ acc) acc₂).mems mn addr width := by
  induction rules generalizing acc₁ acc₂ with
  | nil => exact h
  | cons rule rest ih =>
      exact ih _ _ (rule.body.run_mems_congr_acc σ acc₁ acc₂ mn addr width h)

/-- Exactly the rules whose action may write `(rn, w)`, in original order. -/
def Design.regSupportRules (d : Design) (rn : String) (w : Nat) : List Rule :=
  d.rules.filter fun rule => rule.body.regWrites.contains (rn, w)

/-- Exactly the rules whose action may write memory `mn`, in original order. -/
def Design.memSupportRules (d : Design) (mn : String) : List Rule :=
  d.rules.filter fun rule => rule.body.memWrites.contains mn

private theorem fold_regs_eq_support (rules : List Rule) (σ acc : St)
    (rn : String) (w : Nat) :
    (rules.foldl (fun state rule => rule.body.run σ state) acc).regs rn w =
      ((rules.filter fun rule => rule.body.regWrites.contains (rn, w)).foldl
        (fun state rule => rule.body.run σ state) acc).regs rn w := by
  induction rules generalizing acc with
  | nil => rfl
  | cons rule rest ih =>
      by_cases hw : (rn, w) ∈ rule.body.regWrites
      · simpa [List.contains_eq_mem, hw] using ih (rule.body.run σ acc)
      · rw [List.foldl_cons, ih (rule.body.run σ acc)]
        simp only [List.filter_cons, List.contains_eq_mem, hw]
        exact rulesFold_regs_congr_acc _ σ _ _ rn w
          (rule.body.run_regs_notin rn w hw σ acc)

private theorem fold_mems_eq_support (rules : List Rule) (σ acc : St)
    (mn : String) (addr width : Nat) :
    (rules.foldl (fun state rule => rule.body.run σ state) acc).mems mn addr width =
      ((rules.filter fun rule => rule.body.memWrites.contains mn).foldl
        (fun state rule => rule.body.run σ state) acc).mems mn addr width := by
  induction rules generalizing acc with
  | nil => rfl
  | cons rule rest ih =>
      by_cases hw : mn ∈ rule.body.memWrites
      · simpa [List.contains_eq_mem, hw] using ih (rule.body.run σ acc)
      · rw [List.foldl_cons, ih (rule.body.run σ acc)]
        simp only [List.filter_cons, List.contains_eq_mem, hw]
        exact rulesFold_mems_congr_acc _ σ _ _ mn addr width
          (rule.body.run_mems_notin mn hw σ acc addr width)

/-- Projecting a cycle onto one register needs only the rules that may write
that register. The support is computed from the same action footprint used by
the frame and compiler checks. -/
theorem Design.cycle_regs_eq_support (d : Design) (rn : String) (w : Nat)
    (σ : St) :
    (d.cycle σ).regs rn w =
      ((d.regSupportRules rn w).foldl
        (fun (state : St) (rule : Rule) => rule.body.run σ state) σ).regs rn w :=
  fold_regs_eq_support d.rules σ σ rn w

/-- Memory projection counterpart of `cycle_regs_eq_support`. -/
theorem Design.cycle_mems_eq_support (d : Design) (mn : String)
    (σ : St) (addr width : Nat) :
    (d.cycle σ).mems mn addr width =
      ((d.memSupportRules mn).foldl
        (fun (state : St) (rule : Rule) => rule.body.run σ state) σ).mems mn addr width :=
  fold_mems_eq_support d.rules σ σ mn addr width

/-! ## Supports for multi-coordinate properties

An invariant normally mentions several coordinates. Filtering once for their
union avoids independently replaying the rule list for every projection while
retaining original rule order and last-write-wins semantics.
-/

/-- Rules that may write at least one register coordinate mentioned by a
property, in original design order. -/
def Design.regPropertySupport (d : Design) (coords : List (String × Nat)) :
    List Rule :=
  d.rules.filter fun rule =>
    coords.any fun coord => decide (coord ∈ rule.body.regWrites)

/-- Rules that may write at least one memory named by a property. -/
def Design.memPropertySupport (d : Design) (mems : List String) : List Rule :=
  d.rules.filter fun rule =>
    mems.any fun mem => decide (mem ∈ rule.body.memWrites)

private theorem fold_regs_eq_propertySupport (rules : List Rule)
    (coords : List (String × Nat)) (σ acc : St) (rn : String) (w : Nat)
    (hc : (rn, w) ∈ coords) :
    (rules.foldl (fun state rule => rule.body.run σ state) acc).regs rn w =
      ((rules.filter fun rule =>
          coords.any fun coord => decide (coord ∈ rule.body.regWrites)).foldl
        (fun state rule => rule.body.run σ state) acc).regs rn w := by
  induction rules generalizing acc with
  | nil => rfl
  | cons rule rest ih =>
      by_cases hk :
          (coords.any fun coord => decide (coord ∈ rule.body.regWrites)) = true
      · simpa [hk] using ih (rule.body.run σ acc)
      · have hw : (rn, w) ∉ rule.body.regWrites := by
          intro hw
          apply hk
          rw [List.any_eq_true]
          exact ⟨(rn, w), hc, by exact decide_eq_true hw⟩
        rw [List.foldl_cons, ih (rule.body.run σ acc)]
        simp only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte]
        exact rulesFold_regs_congr_acc _ σ _ _ rn w
          (rule.body.run_regs_notin rn w hw σ acc)

private theorem fold_mems_eq_propertySupport (rules : List Rule)
    (names : List String) (σ acc : St) (mn : String) (addr width : Nat)
    (hc : mn ∈ names) :
    (rules.foldl (fun state rule => rule.body.run σ state) acc).mems mn addr width =
      ((rules.filter fun rule =>
          names.any fun name => decide (name ∈ rule.body.memWrites)).foldl
        (fun state rule => rule.body.run σ state) acc).mems mn addr width := by
  induction rules generalizing acc with
  | nil => rfl
  | cons rule rest ih =>
      by_cases hk :
          (names.any fun name => decide (name ∈ rule.body.memWrites)) = true
      · simpa [hk] using ih (rule.body.run σ acc)
      · have hw : mn ∉ rule.body.memWrites := by
          intro hw
          apply hk
          rw [List.any_eq_true]
          exact ⟨mn, hc, by exact decide_eq_true hw⟩
        rw [List.foldl_cons, ih (rule.body.run σ acc)]
        simp only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte]
        exact rulesFold_mems_congr_acc _ σ _ _ mn addr width
          (rule.body.run_mems_notin mn hw σ acc addr width)

/-- Every register projection named by a property can be evaluated using only
the union of that property's writer rules. -/
theorem Design.cycle_regs_eq_propertySupport (d : Design)
    (coords : List (String × Nat)) (rn : String) (w : Nat)
    (hc : (rn, w) ∈ coords) (σ : St) :
    (d.cycle σ).regs rn w =
      ((d.regPropertySupport coords).foldl
        (fun (state : St) (rule : Rule) => rule.body.run σ state) σ).regs rn w :=
  fold_regs_eq_propertySupport d.rules coords σ σ rn w hc

/-- Memory counterpart of `cycle_regs_eq_propertySupport`. -/
theorem Design.cycle_mems_eq_propertySupport (d : Design)
    (names : List String) (mn : String) (hc : mn ∈ names)
    (σ : St) (addr width : Nat) :
    (d.cycle σ).mems mn addr width =
      ((d.memPropertySupport names).foldl
        (fun (state : St) (rule : Rule) => rule.body.run σ state) σ).mems
          mn addr width :=
  fold_mems_eq_propertySupport d.rules names σ σ mn addr width hc

/-! ## One reduced cycle for a whole state property

The separate register and memory support functions above are convenient for
one projection. An invariant can mention both, so it needs one rule list that
is the ordered union of every named writer. `PropertyFootprint` is that
boundary, and `propertyCycle` is the executable reduced transition.
-/

/-- The state coordinates on which a property depends. Memory footprints are
name/data-width pairs, matching `St.AgreeOn` and the address-conservative
expression footprint. -/
structure PropertyFootprint where
  regs : List (String × Nat) := []
  mems : List (String × Nat) := []
  deriving Repr, DecidableEq, Inhabited

/-- Keep exactly the register and memory writes named by one property
footprint. The two pure projections execute in sequence; their effects are on
disjoint state fields and every expression still reads the same pre-state. -/
def Act.projectFootprint (fp : PropertyFootprint) (action : Act) : Act :=
  smartSeq (action.projectRegs fp.regs) (action.projectMems fp.mems)

/-- Whole-footprint projection preserves every selected register. -/
theorem Act.projectFootprint_run_regs (fp : PropertyFootprint)
    (action : Act) (name : String) (width : Nat)
    (selected : (name, width) ∈ fp.regs) (σ acc : St) :
    ((action.projectFootprint fp).run σ acc).regs name width =
      (action.run σ acc).regs name width := by
  unfold projectFootprint
  rw [smartSeq_run]
  simp only [Act.run]
  rw [projectMems_run_regs]
  exact action.projectRegs_run fp.regs name width selected σ acc

/-- Whole-footprint projection preserves every address of every selected
memory. -/
theorem Act.projectFootprint_run_mems (fp : PropertyFootprint)
    (action : Act) (name : String) (width : Nat)
    (selected : (name, width) ∈ fp.mems) (σ acc : St) (addr : Nat) :
    ((action.projectFootprint fp).run σ acc).mems name addr width =
      (action.run σ acc).mems name addr width := by
  unfold projectFootprint
  rw [smartSeq_run]
  simp only [Act.run]
  have projected := action.projectMems_run fp.mems name width selected σ
    ((action.projectRegs fp.regs).run σ acc) addr
  have sameAccumulator := action.projectRegs_run_mems fp.regs σ acc name addr width
  exact projected.trans
    (action.run_mems_congr_acc σ _ acc name addr width sameAccumulator)

namespace PropertyFootprint

/-- Infer a property footprint from the state reads of an EDSL expression.
This reuses `Expr.readSites`, the same analysis that gates design emission. -/
def ofExpr {w : Nat} (e : Expr w) : PropertyFootprint where
  regs := e.readSites.1
  mems := e.readSites.2

/-- Memory names used for writer support; data widths remain in `mems` for
state agreement. -/
def memNames (fp : PropertyFootprint) : List String := fp.mems.map Prod.fst

/-- A property is supported by `fp` when states agreeing on `fp` either
both satisfy it or both fail it. -/
def Supports (fp : PropertyFootprint) (P : St → Prop) : Prop :=
  ∀ σ τ, St.AgreeOn fp.regs fp.mems σ τ → (P σ ↔ P τ)

/-- Any predicate of an expression's value is supported by its inferred read
footprint. No coordinate list or dependency proof is supplied by the user. -/
theorem supports_eval {w : Nat} (e : Expr w) (Q : BitVec w → Prop) :
    (ofExpr e).Supports (fun σ => Q (e.eval σ)) := by
  intro σ τ h
  have he : e.eval σ = e.eval τ :=
    e.eval_congr_of_agree (by simpa [ofExpr] using h)
  simp [he]

/-- Ordered combination of two footprints. Duplicates are harmless: agreement
and writer selection are membership-based, while preserving order keeps the
definition transparent and cheap to reduce. -/
def append (left right : PropertyFootprint) : PropertyFootprint where
  regs := left.regs ++ right.regs
  mems := left.mems ++ right.mems

theorem Supports.and {left right : PropertyFootprint} {P Q : St → Prop}
    (hP : left.Supports P) (hQ : right.Supports Q) :
    (left.append right).Supports (fun σ => P σ ∧ Q σ) := by
  intro σ τ h
  have h' : St.AgreeOn (left.regs ++ right.regs)
      (left.mems ++ right.mems) σ τ := by
    simpa [append] using h
  exact and_congr (hP σ τ h'.append_left) (hQ σ τ h'.append_right)

theorem Supports.or {left right : PropertyFootprint} {P Q : St → Prop}
    (hP : left.Supports P) (hQ : right.Supports Q) :
    (left.append right).Supports (fun σ => P σ ∨ Q σ) := by
  intro σ τ h
  have h' : St.AgreeOn (left.regs ++ right.regs)
      (left.mems ++ right.mems) σ τ := by
    simpa [append] using h
  exact or_congr (hP σ τ h'.append_left) (hQ σ τ h'.append_right)

theorem Supports.not {fp : PropertyFootprint} {P : St → Prop}
    (hP : fp.Supports P) : fp.Supports (fun σ => ¬ P σ) := by
  intro σ τ h
  exact not_congr (hP σ τ h)

/-- Canonical representative of a state's footprint: named coordinates retain
their values and everything else is zero. A property written over this
projection is footprint-supported by construction. -/
def project (fp : PropertyFootprint) (σ : St) : St where
  regs := fun n w =>
    if (n, w) ∈ fp.regs then σ.regs n w else 0
  mems := fun n a w =>
    if (n, w) ∈ fp.mems then σ.mems n a w else 0

/-- Lift a predicate on canonical projected states to a predicate on ordinary
design states. -/
def lift (fp : PropertyFootprint) (Q : St → Prop) : St → Prop :=
  fun σ => Q (fp.project σ)

theorem project_eq_of_agree (fp : PropertyFootprint) {σ τ : St}
    (h : St.AgreeOn fp.regs fp.mems σ τ) :
    fp.project σ = fp.project τ := by
  unfold project
  congr
  · funext n w
    by_cases hn : (n, w) ∈ fp.regs
    · simp [hn, h.1 n w hn]
    · simp [hn]
  · funext n a w
    by_cases hn : (n, w) ∈ fp.mems
    · simp [hn, h.2 n w hn a]
    · simp [hn]

/-- No manual dependency proof is needed for a lifted property: its canonical
projection erases every coordinate outside the footprint. -/
theorem supports_lift (fp : PropertyFootprint) (Q : St → Prop) :
    fp.Supports (fp.lift Q) := by
  intro σ τ h
  simp only [lift, fp.project_eq_of_agree h]

end PropertyFootprint

/-! ### Propositionally composed expression properties -/

/-- A state property assembled from predicates of typed EDSL expressions.
Unlike a single `Expr 1`, atoms may have different widths, and the logical
shape remains in `Prop`; only their state dependencies are combined. -/
inductive ExprProperty where
  | truth
  | atom {w : Nat} (expr : Expr w) (accepts : BitVec w → Prop)
  | and (left right : ExprProperty)
  | or (left right : ExprProperty)
  | not (property : ExprProperty)

namespace ExprProperty

/-- Proposition denoted by a composed expression property in a state. -/
def eval : ExprProperty → St → Prop
  | .truth, _ => True
  | .atom expr accepts, σ => accepts (expr.eval σ)
  | .and left right, σ => left.eval σ ∧ right.eval σ
  | .or left right, σ => left.eval σ ∨ right.eval σ
  | .not property, σ => ¬ property.eval σ

/-- Complete footprint, derived structurally from every expression atom. -/
def footprint : ExprProperty → PropertyFootprint
  | .truth => {}
  | .atom expr _ => .ofExpr expr
  | .and left right => left.footprint.append right.footprint
  | .or left right => left.footprint.append right.footprint
  | .not property => property.footprint

/-- The derived footprint supports the described property. This is the
compositional extension of `PropertyFootprint.supports_eval`. -/
theorem supports : ∀ property : ExprProperty,
    property.footprint.Supports property.eval
  | .truth => by
      intro _ _ _
      simp [eval]
  | .atom expr accepts => PropertyFootprint.supports_eval expr accepts
  | .and left right => (supports left).and (supports right)
  | .or left right => (supports left).or (supports right)
  | .not property => (supports property).not

/-- Conjoin a list of heterogeneous expression properties.  The empty list
denotes `True`, making generated collections usable without a special head
case. -/
def all (properties : List ExprProperty) : ExprProperty :=
  properties.foldr .and .truth

end ExprProperty

/-! ### General checked transition properties

`TransitionProperty` describes relations between a pre-state and a post-state
using typed Loom expressions.  It deliberately knows nothing about scheduling,
pipelines, instructions, or any other machine policy.  Its footprint and
support theorem are derived structurally, so a client cannot state a property
and accidentally omit one of the coordinates on which it depends.
-/

/-- A propositionally composed, typed relation between two design states. -/
inductive TransitionProperty where
  | truth
  | atom {beforeWidth afterWidth : Nat}
      (before : Expr beforeWidth) (after : Expr afterWidth)
      (accepts : BitVec beforeWidth → BitVec afterWidth → Prop)
  | and (left right : TransitionProperty)
  | or (left right : TransitionProperty)
  | not (property : TransitionProperty)

namespace TransitionProperty

/-- Proposition denoted by a transition property on a before/after pair. -/
def eval : TransitionProperty → St → St → Prop
  | .truth, _, _ => True
  | .atom before after accepts, σ, τ =>
      accepts (before.eval σ) (after.eval τ)
  | .and left right, σ, τ => left.eval σ τ ∧ right.eval σ τ
  | .or left right, σ, τ => left.eval σ τ ∨ right.eval σ τ
  | .not property, σ, τ => ¬ property.eval σ τ

/-- Complete union of all pre-state and post-state expression reads. -/
def footprint : TransitionProperty → PropertyFootprint
  | .truth => {}
  | .atom before after _ =>
      (PropertyFootprint.ofExpr before).append (.ofExpr after)
  | .and left right => left.footprint.append right.footprint
  | .or left right => left.footprint.append right.footprint
  | .not property => property.footprint

/-- Agreement on the inferred footprint for both sides preserves the relation. -/
theorem supports : ∀ property : TransitionProperty,
    ∀ {σ σ' τ τ' : St},
      St.AgreeOn property.footprint.regs property.footprint.mems σ σ' →
      St.AgreeOn property.footprint.regs property.footprint.mems τ τ' →
      (property.eval σ τ ↔ property.eval σ' τ')
  | .truth, _, _, _, _, _, _ => by simp [eval]
  | .atom before after accepts, σ, σ', τ, τ', hbefore, hafter => by
      simp only [footprint] at hbefore hafter
      have hb : before.eval σ = before.eval σ' :=
        before.eval_congr_of_agree hbefore.append_left
      have ha : after.eval τ = after.eval τ' :=
        after.eval_congr_of_agree hafter.append_right
      simp [eval, hb, ha]
  | .and left right, σ, σ', τ, τ', hbefore, hafter => by
      simp only [footprint] at hbefore hafter
      rw [eval, eval]
      exact and_congr
        (supports left hbefore.append_left hafter.append_left)
        (supports right hbefore.append_right hafter.append_right)
  | .or left right, σ, σ', τ, τ', hbefore, hafter => by
      simp only [footprint] at hbefore hafter
      rw [eval, eval]
      exact or_congr
        (supports left hbefore.append_left hafter.append_left)
        (supports right hbefore.append_right hafter.append_right)
  | .not property, σ, σ', τ, τ', hbefore, hafter => by
      rw [eval, eval]
      exact not_congr (supports property hbefore hafter)

/-- Agreement only on the post-state is enough when the pre-state is shared. -/
theorem supportsAfter (property : TransitionProperty) {σ τ τ' : St}
    (h : St.AgreeOn property.footprint.regs property.footprint.mems τ τ') :
    (property.eval σ τ ↔ property.eval σ τ') :=
  property.supports St.AgreeOn.refl h

/-- Conjoin a generated collection of transition properties. -/
def all (properties : List TransitionProperty) : TransitionProperty :=
  properties.foldr .and .truth

/-- A standard relational atom: an expression has the same value before and
after the transition. -/
def unchanged {w : Nat} (expr : Expr w) : TransitionProperty :=
  .atom expr expr (· = ·)

/-- A transition property is reflexive when every state is related to itself. -/
def Reflexive (property : TransitionProperty) : Prop :=
  ∀ σ, property.eval σ σ

theorem unchanged_reflexive {w : Nat} (expr : Expr w) :
    (unchanged expr).Reflexive := by
  intro σ
  rfl

end TransitionProperty

/-- Generic action-level frame rule for checked transition properties. If an
action writes none of the inferred coordinates and the relation is reflexive,
then running the action from a state satisfies that relation. -/
theorem Act.satisfiesTransition_of_unwritten (action : Act)
    (property : TransitionProperty)
    (hregs : ∀ coord ∈ property.footprint.regs,
      coord ∉ action.regWrites)
    (hmems : ∀ coord ∈ property.footprint.mems,
      coord.1 ∉ action.memWrites)
    (hrefl : property.Reflexive) (σ : St) :
    property.eval σ (action.run σ σ) := by
  have hagree : St.AgreeOn property.footprint.regs property.footprint.mems
      (action.run σ σ) σ := by
    constructor
    · intro name width selected
      exact action.run_regs_notin name width
        (hregs (name, width) selected) σ σ
    · intro name width selected addr
      exact action.run_mems_notin name (hmems (name, width) selected)
        σ σ addr width
  exact (property.supportsAfter hagree).2 (hrefl σ)

/-! ### Footprint declaration validation

A typo in a footprint is sound but useless: it selects no real state and can
make a property cone look artificially empty. These checks turn that into a
named obligation before the proof starts.
-/

/-- Property register/input coordinates absent from the design or declared at
a different width. -/
def Design.invalidPropertyRegs (d : Design) (fp : PropertyFootprint) :
    List (String × Nat) :=
  fp.regs.filter fun coord =>
    !(d.regs.any fun r => r.name == coord.1 && r.width == coord.2) &&
    !(d.inputs.any fun i => i.name == coord.1 && i.width == coord.2)

/-- Property memory coordinates absent from the design or declared at a
different data width. -/
def Design.invalidPropertyMems (d : Design) (fp : PropertyFootprint) :
    List (String × Nat) :=
  fp.mems.filter fun coord =>
    !(d.mems.any fun m => m.name == coord.1 && m.dataWidth == coord.2)

/-- Every coordinate in a property footprint resolves at its stated width. -/
def Design.propertyFootprintOkB (d : Design) (fp : PropertyFootprint) : Bool :=
  (d.invalidPropertyRegs fp).isEmpty &&
  (d.invalidPropertyMems fp).isEmpty

/-- Named validation report, empty exactly when `propertyFootprintOkB` is
true. -/
def Design.propertyFootprintReport (d : Design) (fp : PropertyFootprint) :
    String :=
  let badRegs := d.invalidPropertyRegs fp
  let badMems := d.invalidPropertyMems fp
  if badRegs.isEmpty && badMems.isEmpty then ""
  else
    s!"{d.name}: invalid property footprint" ++
    (if badRegs.isEmpty then "" else s!"\n  registers/inputs: {badRegs}") ++
    (if badMems.isEmpty then "" else s!"\n  memories: {badMems}")

/-- Fail-closed IO boundary for tools that consume a property footprint. -/
def Design.assertPropertyFootprint (d : Design) (fp : PropertyFootprint) :
    IO Unit := do
  let report := d.propertyFootprintReport fp
  if report ≠ "" then throw <| IO.userError report

/-- The original-order union of all register and memory writers relevant to a
property footprint. -/
def Design.propertySupportRules (d : Design) (fp : PropertyFootprint) :
    List Rule :=
  d.rules.filter fun rule =>
    (fp.regs.any fun coord => decide (coord ∈ rule.body.regWrites)) ||
    (fp.memNames.any fun name => decide (name ∈ rule.body.memWrites))

/-- Execute only a property's inferred writer cone, retaining the ordinary D9
pre-cycle-read and ordered last-write-wins semantics. -/
def Design.propertyCycle (d : Design) (fp : PropertyFootprint) (σ : St) : St :=
  (d.propertySupportRules fp).foldl
    (fun state rule => rule.body.run σ state) σ

/-- Execute the inferred writer cone after erasing every write outside the
property footprint inside each retained rule. -/
def Design.propertyProjectedCycle (d : Design) (fp : PropertyFootprint)
    (σ : St) : St :=
  (d.propertySupportRules fp).foldl
    (fun state rule => (rule.body.projectFootprint fp).run σ state) σ

private theorem fold_projectFootprint_regs
    (rules : List Rule) (fp : PropertyFootprint) (σ accProjected accFull : St)
    (name : String) (width : Nat) (selected : (name, width) ∈ fp.regs)
    (accAgree : accProjected.regs name width = accFull.regs name width) :
    (rules.foldl
      (fun state rule => (rule.body.projectFootprint fp).run σ state)
      accProjected).regs name width =
    (rules.foldl (fun state rule => rule.body.run σ state) accFull).regs
      name width := by
  induction rules generalizing accProjected accFull with
  | nil => exact accAgree
  | cons rule rest ih =>
      apply ih
      exact (rule.body.projectFootprint_run_regs fp name width selected σ
        accProjected).trans
        (rule.body.run_regs_congr_acc σ accProjected accFull name width accAgree)

private theorem fold_projectFootprint_mems
    (rules : List Rule) (fp : PropertyFootprint) (σ accProjected accFull : St)
    (name : String) (width addr : Nat) (selected : (name, width) ∈ fp.mems)
    (accAgree : accProjected.mems name addr width =
      accFull.mems name addr width) :
    (rules.foldl
      (fun state rule => (rule.body.projectFootprint fp).run σ state)
      accProjected).mems name addr width =
    (rules.foldl (fun state rule => rule.body.run σ state) accFull).mems
      name addr width := by
  induction rules generalizing accProjected accFull with
  | nil => exact accAgree
  | cons rule rest ih =>
      apply ih
      exact (rule.body.projectFootprint_run_mems fp name width selected σ
        accProjected addr).trans
        (rule.body.run_mems_congr_acc σ accProjected accFull name addr width
          accAgree)

/-- Intra-rule projection is observationally exact on the whole property
footprint. -/
theorem Design.propertyCycle_agreeOn_propertyProjectedCycle
    (d : Design) (fp : PropertyFootprint) (σ : St) :
    St.AgreeOn fp.regs fp.mems (d.propertyCycle fp σ)
      (d.propertyProjectedCycle fp σ) := by
  constructor
  · intro name width selected
    exact (fold_projectFootprint_regs (d.propertySupportRules fp) fp σ σ σ
      name width selected rfl).symm
  · intro name width selected addr
    exact (fold_projectFootprint_mems (d.propertySupportRules fp) fp σ σ σ
      name width addr selected rfl).symm

/-- Open-cycle property reduction. Inputs are installed first, exactly as in
`Design.cycleOpen`, and both guards and retained actions read that same poked
pre-cycle state. -/
def Design.propertyCycleOpen (d : Design) (fp : PropertyFootprint)
    (ι : InEnv) (σ : St) : St :=
  d.propertyCycle fp (σ.setInputs d.inputs ι)

/-- Open-cycle form of the intra-rule projected property transition. -/
def Design.propertyProjectedCycleOpen (d : Design) (fp : PropertyFootprint)
    (ι : InEnv) (σ : St) : St :=
  d.propertyProjectedCycle fp (σ.setInputs d.inputs ι)

/-- The writer cone inferred directly from an expression's state reads. -/
def Design.exprPropertySupportRules {w : Nat} (d : Design) (e : Expr w) :
    List Rule :=
  d.propertySupportRules (.ofExpr e)

/-- Execute only the rules that can change an expression's inferred read
footprint. -/
def Design.exprPropertyCycle {w : Nat} (d : Design) (e : Expr w) (σ : St) : St :=
  d.propertyCycle (.ofExpr e) σ

/-- Writer cone inferred from every atom in a propositionally composed
expression property. -/
def Design.propertyExprSupportRules (d : Design) (property : ExprProperty) :
    List Rule :=
  d.propertySupportRules property.footprint

/-- Reduced transition inferred from a propositionally composed expression
property. -/
def Design.propertyExprCycle (d : Design) (property : ExprProperty) (σ : St) : St :=
  d.propertyCycle property.footprint σ

/-- Open reduced transition inferred from a composed expression property. -/
def Design.propertyExprCycleOpen (d : Design) (property : ExprProperty)
    (ι : InEnv) (σ : St) : St :=
  d.propertyCycleOpen property.footprint ι σ

/-- Composed-property transition with both irrelevant rules and irrelevant
writes inside retained rules erased. -/
def Design.projectedPropertyExprCycle (d : Design) (property : ExprProperty)
    (σ : St) : St :=
  d.propertyProjectedCycle property.footprint σ

def Design.projectedPropertyExprCycleOpen (d : Design)
    (property : ExprProperty) (ι : InEnv) (σ : St) : St :=
  d.propertyProjectedCycleOpen property.footprint ι σ

private theorem fold_regs_eq_fullPropertySupport (rules : List Rule)
    (fp : PropertyFootprint) (σ acc : St) (rn : String) (w : Nat)
    (hc : (rn, w) ∈ fp.regs) :
    (rules.foldl (fun state rule => rule.body.run σ state) acc).regs rn w =
      ((rules.filter fun rule =>
          (fp.regs.any fun coord => decide (coord ∈ rule.body.regWrites)) ||
          (fp.memNames.any fun name => decide (name ∈ rule.body.memWrites))).foldl
        (fun state rule => rule.body.run σ state) acc).regs rn w := by
  induction rules generalizing acc with
  | nil => rfl
  | cons rule rest ih =>
      by_cases hk :
          ((fp.regs.any fun coord => decide (coord ∈ rule.body.regWrites)) ||
           (fp.memNames.any fun name => decide (name ∈ rule.body.memWrites))) = true
      · simpa [hk] using ih (rule.body.run σ acc)
      · have hw : (rn, w) ∉ rule.body.regWrites := by
          intro hw
          apply hk
          simp only [Bool.or_eq_true]
          left
          rw [List.any_eq_true]
          exact ⟨(rn, w), hc, decide_eq_true hw⟩
        rw [List.foldl_cons, ih (rule.body.run σ acc)]
        simp only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte]
        exact rulesFold_regs_congr_acc _ σ _ _ rn w
          (rule.body.run_regs_notin rn w hw σ acc)

private theorem fold_mems_eq_fullPropertySupport (rules : List Rule)
    (fp : PropertyFootprint) (σ acc : St) (mn : String) (addr width : Nat)
    (hc : (mn, width) ∈ fp.mems) :
    (rules.foldl (fun state rule => rule.body.run σ state) acc).mems mn addr width =
      ((rules.filter fun rule =>
          (fp.regs.any fun coord => decide (coord ∈ rule.body.regWrites)) ||
          (fp.memNames.any fun name => decide (name ∈ rule.body.memWrites))).foldl
        (fun state rule => rule.body.run σ state) acc).mems mn addr width := by
  induction rules generalizing acc with
  | nil => rfl
  | cons rule rest ih =>
      by_cases hk :
          ((fp.regs.any fun coord => decide (coord ∈ rule.body.regWrites)) ||
           (fp.memNames.any fun name => decide (name ∈ rule.body.memWrites))) = true
      · simpa [hk] using ih (rule.body.run σ acc)
      · have hname : mn ∈ fp.memNames := by
          rw [PropertyFootprint.memNames, List.mem_map]
          exact ⟨(mn, width), hc, rfl⟩
        have hw : mn ∉ rule.body.memWrites := by
          intro hw
          apply hk
          simp only [Bool.or_eq_true]
          right
          rw [List.any_eq_true]
          exact ⟨mn, hname, decide_eq_true hw⟩
        rw [List.foldl_cons, ih (rule.body.run σ acc)]
        simp only [List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte]
        exact rulesFold_mems_congr_acc _ σ _ _ mn addr width
          (rule.body.run_mems_notin mn hw σ acc addr width)

/-- The full and property-reduced cycles agree on every named register. -/
theorem Design.cycle_regs_eq_propertyCycle (d : Design)
    (fp : PropertyFootprint) (rn : String) (w : Nat)
    (hc : (rn, w) ∈ fp.regs) (σ : St) :
    (d.cycle σ).regs rn w = (d.propertyCycle fp σ).regs rn w :=
  fold_regs_eq_fullPropertySupport d.rules fp σ σ rn w hc

/-- The full and property-reduced cycles agree at every address of every named
memory/data-width pair. -/
theorem Design.cycle_mems_eq_propertyCycle (d : Design)
    (fp : PropertyFootprint) (mn : String) (width : Nat)
    (hc : (mn, width) ∈ fp.mems) (σ : St) (addr : Nat) :
    (d.cycle σ).mems mn addr width =
      (d.propertyCycle fp σ).mems mn addr width :=
  fold_mems_eq_fullPropertySupport d.rules fp σ σ mn addr width hc

/-- Central W2 result: the full transition and its inferred property cone are
observationally identical on the property's complete footprint. -/
theorem Design.cycle_agreeOn_propertyCycle (d : Design)
    (fp : PropertyFootprint) (σ : St) :
    St.AgreeOn fp.regs fp.mems (d.cycle σ) (d.propertyCycle fp σ) :=
  ⟨fun rn w hc => d.cycle_regs_eq_propertyCycle fp rn w hc σ,
   fun mn w hc addr => d.cycle_mems_eq_propertyCycle fp mn w hc σ addr⟩

/-- A checked transition property has exactly the same truth value on the full
design cycle and on the writer cone inferred from all of its before/after
expressions.  This is the general `Design` theorem; machine-specific concerns
such as scheduling appear only in properties supplied by clients. -/
theorem Design.transitionProperty_iff_propertyCycle (d : Design)
    (property : TransitionProperty) (σ : St) :
    property.eval σ (d.cycle σ) ↔
      property.eval σ (d.propertyCycle property.footprint σ) :=
  property.supportsAfter (d.cycle_agreeOn_propertyCycle property.footprint σ)

/-- Rule selection and intra-rule write projection compose into one transition
that is exact on the requested footprint. -/
theorem Design.cycle_agreeOn_propertyProjectedCycle (d : Design)
    (fp : PropertyFootprint) (σ : St) :
    St.AgreeOn fp.regs fp.mems (d.cycle σ)
      (d.propertyProjectedCycle fp σ) :=
  (d.cycle_agreeOn_propertyCycle fp σ).trans
    (d.propertyCycle_agreeOn_propertyProjectedCycle fp σ)

/-- Open-cycle counterpart: the environment is applied identically before
the full and property-reduced transitions. -/
theorem Design.cycleOpen_agreeOn_propertyCycleOpen (d : Design)
    (fp : PropertyFootprint) (ι : InEnv) (σ : St) :
    St.AgreeOn fp.regs fp.mems (d.cycleOpen ι σ)
      (d.propertyCycleOpen fp ι σ) := by
  simpa [Design.cycleOpen, Design.propertyCycleOpen] using
    d.cycle_agreeOn_propertyCycle fp (σ.setInputs d.inputs ι)

theorem Design.cycleOpen_agreeOn_propertyProjectedCycleOpen (d : Design)
    (fp : PropertyFootprint) (ι : InEnv) (σ : St) :
    St.AgreeOn fp.regs fp.mems (d.cycleOpen ι σ)
      (d.propertyProjectedCycleOpen fp ι σ) := by
  simpa [Design.cycleOpen, Design.propertyProjectedCycleOpen] using
    d.cycle_agreeOn_propertyProjectedCycle fp (σ.setInputs d.inputs ι)

/-- Proving preservation on the reduced property cycle is sufficient for the
full design cycle. -/
theorem Design.propertyCycle_preserves {d : Design} {fp : PropertyFootprint}
    {P : St → Prop} (hsupport : fp.Supports P) {σ : St}
    (hstep : P σ → P (d.propertyCycle fp σ)) :
    P σ → P (d.cycle σ) := by
  intro hP
  exact (hsupport (d.cycle σ) (d.propertyCycle fp σ)
    (d.cycle_agreeOn_propertyCycle fp σ)).mpr (hstep hP)

/-- Reusable invariant combinator: reset is checked once, and the inductive
step is proved only over the inferred property transition. -/
theorem Design.invariant_of_propertyCycle (d : Design)
    (fp : PropertyFootprint) (P : St → Prop)
    (hsupport : fp.Supports P)
    (hreset : P d.reset)
    (hstep : ∀ σ, P σ → P (d.propertyCycle fp σ)) :
    d.toTSys.Invariant P := by
  apply Loom.TSys.Inductive.invariant
  constructor
  · intro σ hinit
    simp only [Design.toTSys_init_iff] at hinit
    subst σ
    exact hreset
  · intro σ τ hP hcycle
    simp only [Design.toTSys_step_iff] at hcycle
    subst τ
    exact d.propertyCycle_preserves hsupport (hstep σ) hP

/-- Stronger local-proof combinator: retained rules are themselves projected
to the property footprint before the preservation obligation is presented. -/
theorem Design.invariant_of_projectedPropertyCycle (d : Design)
    (fp : PropertyFootprint) (P : St → Prop)
    (hsupport : fp.Supports P)
    (hreset : P d.reset)
    (hstep : ∀ σ, P σ → P (d.propertyProjectedCycle fp σ)) :
    d.toTSys.Invariant P := by
  apply d.invariant_of_propertyCycle fp P hsupport hreset
  intro σ current
  exact (hsupport _ _
    (d.propertyCycle_agreeOn_propertyProjectedCycle fp σ)).2
      (hstep σ current)

/-- Open assume/guarantee form of the fully projected property transition. -/
theorem Design.invariant_of_assumedProjectedPropertyCycleOpen (d : Design)
    (assume : InputAssumption) (fp : PropertyFootprint) (P : St → Prop)
    (hsupport : fp.Supports P)
    (hreset : P d.reset)
    (hstep : ∀ σ ι, P σ → assume σ ι →
      P (d.propertyProjectedCycleOpen fp ι σ)) :
    (d.toAssumedOpenTSys assume).Invariant P := by
  apply d.invariant_of_assumedCycleOpen assume P hreset
  intro σ ι current accepted
  exact (hsupport _ _
    (d.cycleOpen_agreeOn_propertyProjectedCycleOpen fp ι σ)).2
      (hstep σ ι current accepted)

/-- Dependency-by-construction variant: a predicate over canonical projected
states needs no separate `Supports` proof. -/
theorem Design.invariant_of_liftedPropertyCycle (d : Design)
    (fp : PropertyFootprint) (Q : St → Prop)
    (hreset : fp.lift Q d.reset)
    (hstep : ∀ σ, fp.lift Q σ → fp.lift Q (d.propertyCycle fp σ)) :
    d.toTSys.Invariant (fp.lift Q) :=
  d.invariant_of_propertyCycle fp (fp.lift Q) (fp.supports_lift Q)
    hreset hstep

/-- Expression-shaped invariant combinator. `Expr.readSites` supplies the
complete property footprint, so both dependency support and the reduced
writer cone are inferred from `e`. -/
theorem Design.invariant_of_exprPropertyCycle {w : Nat} (d : Design)
    (e : Expr w) (Q : BitVec w → Prop)
    (hreset : Q (e.eval d.reset))
    (hstep : ∀ σ, Q (e.eval σ) → Q (e.eval (d.exprPropertyCycle e σ))) :
    d.toTSys.Invariant (fun σ => Q (e.eval σ)) := by
  apply d.invariant_of_propertyCycle (.ofExpr e) _
      (PropertyFootprint.supports_eval e Q) hreset
  simpa [Design.exprPropertyCycle] using hstep

/-- Compositional expression-property invariant combinator. The logical
description supplies its own complete footprint and support theorem. -/
theorem Design.invariant_of_propertyExprCycle (d : Design)
    (property : ExprProperty)
    (hreset : property.eval d.reset)
    (hstep : ∀ σ, property.eval σ →
      property.eval (d.propertyExprCycle property σ)) :
    d.toTSys.Invariant property.eval := by
  apply d.invariant_of_propertyCycle property.footprint property.eval
      property.supports hreset
  simpa [Design.propertyExprCycle] using hstep

/-- Composed-property invariant whose step sees only selected writes inside
the inferred writer cone. -/
theorem Design.invariant_of_projectedPropertyExprCycle (d : Design)
    (property : ExprProperty)
    (hreset : property.eval d.reset)
    (hstep : ∀ σ, property.eval σ →
      property.eval (d.projectedPropertyExprCycle property σ)) :
    d.toTSys.Invariant property.eval := by
  apply d.invariant_of_projectedPropertyCycle property.footprint property.eval
      property.supports hreset
  simpa [Design.projectedPropertyExprCycle] using hstep

/-- Assume/guarantee invariant combinator for an open design, with the writer
cone still inferred from the composed expression property.  The environment
contract is a visible theorem argument and may depend on the current state. -/
theorem Design.invariant_of_assumedPropertyExprCycleOpen (d : Design)
    (assume : InputAssumption) (property : ExprProperty)
    (hreset : property.eval d.reset)
    (hstep : ∀ σ ι, property.eval σ → assume σ ι →
      property.eval (d.propertyExprCycleOpen property ι σ)) :
    (d.toAssumedOpenTSys assume).Invariant property.eval := by
  apply d.invariant_of_assumedCycleOpen assume property.eval hreset
  intro σ ι current accepted
  apply (property.supports _ _
    (d.cycleOpen_agreeOn_propertyCycleOpen property.footprint ι σ)).mpr
  exact hstep σ ι current accepted

/-- Assume/guarantee composed-property invariant with intra-rule projection. -/
theorem Design.invariant_of_assumedProjectedPropertyExprCycleOpen (d : Design)
    (assume : InputAssumption) (property : ExprProperty)
    (hreset : property.eval d.reset)
    (hstep : ∀ σ ι, property.eval σ → assume σ ι →
      property.eval (d.projectedPropertyExprCycleOpen property ι σ)) :
    (d.toAssumedOpenTSys assume).Invariant property.eval := by
  apply d.invariant_of_assumedProjectedPropertyCycleOpen assume
    property.footprint property.eval property.supports hreset
  simpa [Design.projectedPropertyExprCycleOpen] using hstep

/-! ## Discharging the side conditions by evaluation

A frame rule is only labour-saving if its hypothesis is cheaper to establish
than the property it frames. `∀ r ∈ d.rules, (rn, w) ∉ r.body.regWrites` is a
quantified statement over every rule of a design that, for `lnp64mini`, has
hundreds of them — proving it by hand would cost more than it saves.

These Boolean mirrors are computable, so the hypothesis is discharged by
`decide` (or `native_decide` on a large design) and the frame rule becomes a
one-liner. This is the "support inference" half of W2: the analysis runs, the
proof consumes its result. -/

/-- Computable: no rule of `d` writes register `(rn, w)`. -/
def Design.regUnwrittenB (d : Design) (rn : String) (w : Nat) : Bool :=
  d.rules.all fun r => !(r.body.regWrites.contains (rn, w))

/-- Computable: no rule of `d` writes memory `mn`. -/
def Design.memUnwrittenB (d : Design) (mn : String) : Bool :=
  d.rules.all fun r => !(r.body.memWrites.contains mn)

theorem Design.cycle_regs_of_unwrittenB {d : Design} {rn : String} {w : Nat}
    (h : d.regUnwrittenB rn w = true) (σ : St) :
    (d.cycle σ).regs rn w = σ.regs rn w := by
  refine d.cycle_regs_notin rn w (fun r hr hmem => ?_) σ
  have := (List.all_eq_true.mp h) r hr
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  exact this hmem

theorem Design.cycle_mems_of_unwrittenB {d : Design} {mn : String}
    (h : d.memUnwrittenB mn = true) (σ : St) (ad w : Nat) :
    (d.cycle σ).mems mn ad w = σ.mems mn ad w := by
  refine d.cycle_mems_notin mn (fun r hr hmem => ?_) σ ad w
  have := (List.all_eq_true.mp h) r hr
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  exact this hmem

/-! ## The rules firing on a design

A worked check that the API is usable as advertised: a two-register design
whose only rule bumps `a`. The frame rule then says `b` survives a cycle, and
the hypothesis is discharged by `decide` — no induction over the rule list at
the use site, which is the entire point.

`Expr.eval_congr_of_agree` is exercised on the other side: two states differing
*only* in `b` agree on the footprint of an expression that reads only `a`, so
the expression cannot tell them apart. -/

private def frameDemo : Design where
  name := "framedemo"
  regs := [{ name := "a", width := 8, init := 0 }, { name := "b", width := 8, init := 7 }]
  mems := []
  rules := [{ name := "bump_a", body := .write 8 "a" (.add (.reg 8 "a") (.lit 1#8)) }]
  inputs := []
  outputs := ["a", "b"]

-- The side condition is a computation, not a proof obligation.
example : frameDemo.regUnwrittenB "b" 8 = true := by decide

/-- `b` is framed out of the cycle: one `decide`, no reasoning about `bump_a`. -/
example (σ : St) : (frameDemo.cycle σ).regs "b" 8 = σ.regs "b" 8 :=
  frameDemo.cycle_regs_of_unwrittenB (by decide) σ

/-- And the design does not vacuously preserve everything: `a` *is* written, so
the checker refuses it. A frame rule that fired on every register would be
useless, so this is the half worth pinning down. -/
example : frameDemo.regUnwrittenB "a" 8 = false := by decide

/-- Read side: an expression over `a` alone cannot observe a change to `b`. -/
example (σ : St) (v : BitVec 8) :
    (Expr.add (.reg 8 "a") (.lit 3#8)).eval σ
      = (Expr.add (.reg 8 "a") (.lit 3#8)).eval { σ with regs := σ.regs.set "b" v } := by
  refine Expr.eval_congr_of_agree _ ⟨fun n w hn => ?_, fun m w hm => by simp [Expr.readSites] at hm⟩
  -- the footprint is exactly [("a", 8)], and `RegEnv.set "b"` leaves it alone
  simp only [Expr.readSites, List.append_nil, List.mem_singleton] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hn
  simp [RegEnv.set]

end Loom.Hw
