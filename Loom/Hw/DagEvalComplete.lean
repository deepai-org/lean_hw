-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.DagEval
import Std.Data.HashMap.Lemmas

/-!
# Completeness of certified DAG preparation

`DagEval` already proves that every accepted structural certificate is sound.
This module proves the converse needed by the public preparation contract:
the hash-consing lowering always constructs a certificate that its independent
checker accepts.  Hash-table correctness affects preparation cost, not whether
a well-formed Design has a certified optimized simulator.
-/

namespace Loom.Hw.DagEval

open Loom.Hw

/-! ## Completeness of the independent checker -/

theorem nodesWFB_complete {nodes : Array Node} (h : NodesWF nodes) :
    nodesWFB nodes = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hil : i < nodes.size := List.mem_range.mp hi
  apply List.all_eq_true.mpr
  intro r hr
  apply decide_eq_true
  apply h i hil r
  simpa [Array.getD_getElem?, hil] using hr

theorem checkExpr_complete_some {nodes : Array Node} {root : Nat} {e : FExpr}
    (h : ExprMatch nodes root e) :
    ∃ checked, checkExpr nodes root e = some checked := by
  induction h with
  | lit bound node =>
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.lit bound node⟩, ?_⟩
      simp [checkExpr, bound, node']
  | reg bound node =>
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.reg bound node⟩, ?_⟩
      simp [checkExpr, bound, node']
  | memRead bound node before addr ih =>
      obtain ⟨checked, hchecked⟩ := ih
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.memRead bound node before checked.proof⟩, ?_⟩
      simp [checkExpr, bound, node', before, hchecked]
  | and bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.and bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | or bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.or bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | xor bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.xor bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | not bound node before arg ih =>
      obtain ⟨checked, hchecked⟩ := ih
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.not bound node before checked.proof⟩, ?_⟩
      simp [checkExpr, bound, node', before, hchecked, checkExpr.checkUnary]
  | add bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.add bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | sub bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.sub bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | mul bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.mul bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | udiv bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.udiv bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | urem bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.urem bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | shl bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.shl bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | shr bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.shr bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | eq bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.eq bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | ult bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.ult bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | slt bound node ab left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.slt bound node ab cl.proof cr.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ab, hcl, hcr, checkExpr.checkBin]
  | mux bound node ctf cond yes no ihc iht ihf =>
      obtain ⟨cc, hcc⟩ := ihc
      obtain ⟨ct, hct⟩ := iht
      obtain ⟨cf, hcf⟩ := ihf
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.mux bound node ctf cc.proof ct.proof cf.proof⟩, ?_⟩
      simp [checkExpr, bound, node', ctf, hcc, hct, hcf]
  | slice bound node before arg ih =>
      obtain ⟨checked, hchecked⟩ := ih
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.slice bound node before checked.proof⟩, ?_⟩
      simp [checkExpr, bound, node', before, hchecked, checkExpr.checkUnary]
  | zext bound node before arg ih =>
      obtain ⟨checked, hchecked⟩ := ih
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.zext bound node before checked.proof⟩, ?_⟩
      simp [checkExpr, bound, node', before, hchecked, checkExpr.checkUnary]
  | sext bound node before arg ih =>
      obtain ⟨checked, hchecked⟩ := ih
      have node' := node
      simp [bound] at node'
      refine ⟨⟨.sext bound node before checked.proof⟩, ?_⟩
      simp [checkExpr, bound, node', before, hchecked, checkExpr.checkUnary]

theorem checkExpr_complete {nodes : Array Node} {root : Nat} {e : FExpr}
    (h : ExprMatch nodes root e) : (checkExpr nodes root e).isSome = true := by
  obtain ⟨checked, hchecked⟩ := checkExpr_complete_some h
  simp [hchecked]

theorem checkAct_complete_some {nodes : Array Node} {a : Act} {fa : FAct}
    (h : ActMatch nodes a fa) : ∃ checked, checkAct nodes a fa = some checked := by
  induction h with
  | skip => exact ⟨_, rfl⟩
  | seq left right ihl ihr =>
      obtain ⟨cl, hcl⟩ := ihl
      obtain ⟨cr, hcr⟩ := ihr
      refine ⟨⟨.seq cl.proof cr.proof⟩, ?_⟩
      simp [checkAct, hcl, hcr]
  | ite cond yes no ihy ihn =>
      obtain ⟨cc, hcc⟩ := checkExpr_complete_some cond
      obtain ⟨cy, hcy⟩ := ihy
      obtain ⟨cn, hcn⟩ := ihn
      refine ⟨⟨.ite cc.proof cy.proof cn.proof⟩, ?_⟩
      simp [checkAct, hcc, hcy, hcn]
  | write value =>
      obtain ⟨checked, hchecked⟩ := checkExpr_complete_some value
      refine ⟨⟨.write checked.proof⟩, ?_⟩
      simp [checkAct, hchecked]
  | memWrite addr value =>
      obtain ⟨ca, hca⟩ := checkExpr_complete_some addr
      obtain ⟨cv, hcv⟩ := checkExpr_complete_some value
      refine ⟨⟨.memWrite ca.proof cv.proof⟩, ?_⟩
      simp [checkAct, hca, hcv]

theorem checkAct_complete {nodes : Array Node} {a : Act} {fa : FAct}
    (h : ActMatch nodes a fa) : (checkAct nodes a fa).isSome = true := by
  obtain ⟨checked, hchecked⟩ := checkAct_complete_some h
  simp [hchecked]

theorem checkActs_complete_some {nodes : Array Node} {acts : List Act}
    {facts : List FAct} (h : ActsMatch nodes acts facts) :
    ∃ checked, checkActs nodes acts facts = some checked := by
  induction h with
  | nil => exact ⟨_, rfl⟩
  | cons head tail ih =>
      obtain ⟨ch, hch⟩ := checkAct_complete_some head
      obtain ⟨ct, hct⟩ := ih
      refine ⟨⟨.cons ch.proof ct.proof⟩, ?_⟩
      simp [checkActs, hch, hct]

theorem checkActs_complete {nodes : Array Node} {acts : List Act}
    {facts : List FAct} (h : ActsMatch nodes acts facts) :
    (checkActs nodes acts facts).isSome = true := by
  obtain ⟨checked, hchecked⟩ := checkActs_complete_some h
  simp [hchecked]

theorem checkCertificate_complete {fd : FastDesign} {d : Design}
    (cert : Certificate fd d) : (checkCertificate fd d).isSome = true := by
  unfold checkCertificate
  have hn := nodesWFB_complete cert.nodes
  obtain ⟨checked, hchecked⟩ := checkActs_complete_some cert.acts
  simp [hn, hchecked, cert.slots]

/-! ## Prefix transport for incrementally built node arrays -/

/-- `small` is the exact initial segment of `large`. -/
structure NodesPrefix (small large : Array Node) : Prop where
  size : small.size ≤ large.size
  get : ∀ i (hi : i < small.size),
    large[i]'(Nat.lt_of_lt_of_le hi size) = small[i]

namespace NodesPrefix

theorem refl (nodes : Array Node) : NodesPrefix nodes nodes :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem trans {a b c : Array Node} (hab : NodesPrefix a b)
    (hbc : NodesPrefix b c) : NodesPrefix a c where
  size := Nat.le_trans hab.size hbc.size
  get i hi := by
    rw [hbc.get i (Nat.lt_of_lt_of_le hi hab.size), hab.get i hi]

theorem push (nodes : Array Node) (node : Node) :
    NodesPrefix nodes (nodes.push node) where
  size := by simp
  get i hi := by simp [Array.getElem_push, hi]

theorem getD {small large : Array Node} (pref : NodesPrefix small large)
    (i : Nat) (hi : i < small.size) :
    large.getD i default = small.getD i default := by
  have hil : i < large.size := Nat.lt_of_lt_of_le hi pref.size
  simp [hi, hil, pref.get i hi]

end NodesPrefix

theorem ExprMatch.mono {small large : Array Node} {root : Nat} {e : FExpr}
    (h : ExprMatch small root e) (pref : NodesPrefix small large) :
    ExprMatch large root e := by
  induction h with
  | lit bound node =>
      exact .lit (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node)
  | reg bound node =>
      exact .reg (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node)
  | memRead bound node before addr ih =>
      exact .memRead (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) before ih
  | and bound node ab left right ihl ihr =>
      exact .and (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | or bound node ab left right ihl ihr =>
      exact .or (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | xor bound node ab left right ihl ihr =>
      exact .xor (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | not bound node before arg ih =>
      exact .not (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) before ih
  | add bound node ab left right ihl ihr =>
      exact .add (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | sub bound node ab left right ihl ihr =>
      exact .sub (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | mul bound node ab left right ihl ihr =>
      exact .mul (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | udiv bound node ab left right ihl ihr =>
      exact .udiv (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | urem bound node ab left right ihl ihr =>
      exact .urem (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | shl bound node ab left right ihl ihr =>
      exact .shl (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | shr bound node ab left right ihl ihr =>
      exact .shr (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | eq bound node ab left right ihl ihr =>
      exact .eq (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | ult bound node ab left right ihl ihr =>
      exact .ult (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | slt bound node ab left right ihl ihr =>
      exact .slt (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ab ihl ihr
  | mux bound node ctf cond yes no ihc iht ihf =>
      exact .mux (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) ctf ihc iht ihf
  | slice bound node before arg ih =>
      exact .slice (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) before ih
  | zext bound node before arg ih =>
      exact .zext (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) before ih
  | sext bound node before arg ih =>
      exact .sext (Nat.lt_of_lt_of_le bound pref.size)
        (by exact (pref.getD _ bound).trans node) before ih

theorem ExprMatch.root_lt {nodes : Array Node} {root : Nat} {e : FExpr}
    (h : ExprMatch nodes root e) : root < nodes.size := by cases h <;> assumption

/-! ## Correctness of hash-consing construction -/

structure Build.Valid (s : Build) : Prop where
  nodes : NodesWF s.nodes
  seen : ∀ e i, s.seen.get? e = some i → ExprMatch s.nodes i e

theorem NodesWF.push {nodes : Array Node} (hwf : NodesWF nodes) (n : Node)
    (hrefs : ∀ r, r ∈ n.refs → r < nodes.size) : NodesWF (nodes.push n) := by
  intro i hi r hr
  by_cases hold : i < nodes.size
  · have hnode : (nodes.push n)[i] = nodes[i] := by simp [Array.getElem_push, hold]
    apply hwf i hold r
    simpa [hnode] using hr
  · have hle : i ≤ nodes.size := Nat.le_of_lt_succ (by simpa using hi)
    have hiEq : i = nodes.size := Nat.le_antisymm hle (Nat.le_of_not_gt hold)
    subst i
    simpa using hrefs r (by simpa using hr)

theorem Build.Valid.empty : Build.Valid ({} : Build) := by
  constructor
  · intro i hi
    simp at hi
  · intro e i h
    simp at h

theorem Build.Valid.add {s : Build} (valid : s.Valid) {e : FExpr} {n : Node}
    (hrefs : ∀ r, r ∈ n.refs → r < s.nodes.size)
    (hmatch : ExprMatch (s.nodes.push n) s.nodes.size e) :
    (s.add e n).2.Valid := by
  constructor
  · exact valid.nodes.push n hrefs
  · intro e' i hget
    simp only [Build.add] at hget ⊢
    rw [Std.HashMap.get?_eq_getElem?] at hget
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · have heq : e = e' := eq_of_beq (by assumption)
      subst e'
      simp at hget
      subst i
      exact hmatch
    · exact (valid.seen e' i hget).mono (NodesPrefix.push _ _)

structure InternResult (e : FExpr) (start : Build) (root : Nat)
    (finish : Build) : Prop where
  eq : intern e start = (root, finish)
  valid : finish.Valid
  nodesPrefix : NodesPrefix start.nodes finish.nodes
  exprMatch : ExprMatch finish.nodes root e

theorem intern_complete (e : FExpr) (s : Build) (valid : s.Valid) :
    ∃ root finish, InternResult e s root finish := by
  induction e generalizing s with
  | lit v =>
      cases hseen : s.seen.get? (.lit v) with
      | some i =>
        have hseen' : s.seen[FExpr.lit v]? = some i := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨i, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.lit v]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        let finish := (s.add (.lit v) (.lit v)).2
        have hbound : s.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s.nodes.size default = .lit v := by
          simp [finish, Build.add]
        have hmatch : ExprMatch finish.nodes s.nodes.size (.lit v) := .lit hbound hnode
        exact ⟨s.nodes.size, finish, by simp [intern, hseen', finish, Build.add],
          valid.add (by simp [Node.refs]) hmatch, NodesPrefix.push _ _, hmatch⟩
  | reg i =>
      cases hseen : s.seen.get? (.reg i) with
      | some root =>
        have hseen' : s.seen[FExpr.reg i]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.reg i]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        let finish := (s.add (.reg i) (.reg i)).2
        have hbound : s.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s.nodes.size default = .reg i := by
          simp [finish, Build.add]
        have hmatch : ExprMatch finish.nodes s.nodes.size (.reg i) := .reg hbound hnode
        exact ⟨s.nodes.size, finish, by simp [intern, hseen', finish, Build.add],
          valid.add (by simp [Node.refs]) hmatch, NodesPrefix.push _ _, hmatch⟩
  | memRead base a ih =>
      cases hseen : s.seen.get? (.memRead base a) with
      | some root =>
        have hseen' : s.seen[FExpr.memRead base a]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.memRead base a]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := ih s valid
        let finish := (s1.add (.memRead base a) (.memRead base ia)).2
        have hbound : s1.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s1.nodes.size default = .memRead base ia := by
          simp [finish, Build.add]
        have harg : ExprMatch finish.nodes ia a :=
          ra.exprMatch.mono (NodesPrefix.push _ _)
        have hmatch : ExprMatch finish.nodes s1.nodes.size (.memRead base a) :=
          .memRead hbound hnode ra.exprMatch.root_lt harg
        exact ⟨s1.nodes.size, finish,
          by simp [intern, hseen', ra.eq, finish, Build.add],
          ra.valid.add (by simp [Node.refs, ra.exprMatch.root_lt]) hmatch,
          ra.nodesPrefix.trans (NodesPrefix.push _ _), hmatch⟩
  | and a b iha ihb =>
      cases hseen : s.seen.get? (.and a b) with
      | some root =>
        have hseen' : s.seen[FExpr.and a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.and a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.and a b) (.and ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .and ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.and a b) :=
          .and hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | or a b iha ihb =>
      cases hseen : s.seen.get? (.or a b) with
      | some root =>
        have hseen' : s.seen[FExpr.or a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.or a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.or a b) (.or ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .or ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.or a b) :=
          .or hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | xor a b iha ihb =>
      cases hseen : s.seen.get? (.xor a b) with
      | some root =>
        have hseen' : s.seen[FExpr.xor a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.xor a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.xor a b) (.xor ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .xor ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.xor a b) :=
          .xor hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | not mask a ih =>
      cases hseen : s.seen.get? (.not mask a) with
      | some root =>
        have hseen' : s.seen[FExpr.not mask a]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.not mask a]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := ih s valid
        let finish := (s1.add (.not mask a) (.not mask ia)).2
        have hbound : s1.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s1.nodes.size default = .not mask ia := by
          simp [finish, Build.add]
        have harg : ExprMatch finish.nodes ia a :=
          ra.exprMatch.mono (NodesPrefix.push _ _)
        have hmatch : ExprMatch finish.nodes s1.nodes.size (.not mask a) :=
          .not hbound hnode ra.exprMatch.root_lt harg
        exact ⟨s1.nodes.size, finish,
          by simp [intern, hseen', ra.eq, finish, Build.add],
          ra.valid.add (by simp [Node.refs, ra.exprMatch.root_lt]) hmatch,
          ra.nodesPrefix.trans (NodesPrefix.push _ _), hmatch⟩
  | add m a b iha ihb =>
      cases hseen : s.seen.get? (.add m a b) with
      | some root =>
        have hseen' : s.seen[FExpr.add m a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.add m a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.add m a b) (.add m ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .add m ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.add m a b) :=
          .add hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | sub m a b iha ihb =>
      cases hseen : s.seen.get? (.sub m a b) with
      | some root =>
        have hseen' : s.seen[FExpr.sub m a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.sub m a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.sub m a b) (.sub m ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .sub m ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.sub m a b) :=
          .sub hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | mul m a b iha ihb =>
      cases hseen : s.seen.get? (.mul m a b) with
      | some root =>
        have hseen' : s.seen[FExpr.mul m a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.mul m a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.mul m a b) (.mul m ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .mul m ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.mul m a b) :=
          .mul hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | udiv a b iha ihb =>
      cases hseen : s.seen.get? (.udiv a b) with
      | some root =>
        have hseen' : s.seen[FExpr.udiv a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.udiv a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.udiv a b) (.udiv ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .udiv ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.udiv a b) :=
          .udiv hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | urem a b iha ihb =>
      cases hseen : s.seen.get? (.urem a b) with
      | some root =>
        have hseen' : s.seen[FExpr.urem a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.urem a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.urem a b) (.urem ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .urem ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.urem a b) :=
          .urem hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | shl w m a b iha ihb =>
      cases hseen : s.seen.get? (.shl w m a b) with
      | some root =>
        have hseen' : s.seen[FExpr.shl w m a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.shl w m a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.shl w m a b) (.shl w m ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .shl w m ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.shl w m a b) :=
          .shl hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | shr w a b iha ihb =>
      cases hseen : s.seen.get? (.shr w a b) with
      | some root =>
        have hseen' : s.seen[FExpr.shr w a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.shr w a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.shr w a b) (.shr w ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .shr w ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.shr w a b) :=
          .shr hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | eq a b iha ihb =>
      cases hseen : s.seen.get? (.eq a b) with
      | some root =>
        have hseen' : s.seen[FExpr.eq a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.eq a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.eq a b) (.eq ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .eq ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.eq a b) :=
          .eq hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | ult a b iha ihb =>
      cases hseen : s.seen.get? (.ult a b) with
      | some root =>
        have hseen' : s.seen[FExpr.ult a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.ult a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.ult a b) (.ult ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .ult ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.ult a b) :=
          .ult hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | slt h a b iha ihb =>
      cases hseen : s.seen.get? (.slt h a b) with
      | some root =>
        have hseen' : s.seen[FExpr.slt h a b]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.slt h a b]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := iha s valid
        obtain ⟨ib, s2, rb⟩ := ihb s1 ra.valid
        let finish := (s2.add (.slt h a b) (.slt h ia ib)).2
        have hbound : s2.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s2.nodes.size default = .slt h ia ib := by
          simp [finish, Build.add]
        have hleft : ExprMatch finish.nodes ia a :=
          (ra.exprMatch.mono rb.nodesPrefix).mono (NodesPrefix.push _ _)
        have hright : ExprMatch finish.nodes ib b :=
          rb.exprMatch.mono (NodesPrefix.push _ _)
        have hab : ia < s2.nodes.size ∧ ib < s2.nodes.size :=
          ⟨(ra.exprMatch.mono rb.nodesPrefix).root_lt, rb.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s2.nodes.size (.slt h a b) :=
          .slt hbound hnode hab hleft hright
        exact ⟨s2.nodes.size, finish,
          by simp [intern, hseen', ra.eq, rb.eq, finish, Build.add],
          rb.valid.add (by simp [Node.refs, hab]) hmatch,
          (ra.nodesPrefix.trans rb.nodesPrefix).trans (NodesPrefix.push _ _), hmatch⟩
  | mux c t f ihc iht ihf =>
      cases hseen : s.seen.get? (.mux c t f) with
      | some root =>
        have hseen' : s.seen[FExpr.mux c t f]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.mux c t f]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ic, s1, rc⟩ := ihc s valid
        obtain ⟨it, s2, rt⟩ := iht s1 rc.valid
        obtain ⟨if_, s3, rf⟩ := ihf s2 rt.valid
        let finish := (s3.add (.mux c t f) (.mux ic it if_)).2
        have hbound : s3.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s3.nodes.size default = .mux ic it if_ := by
          simp [finish, Build.add]
        have hcond : ExprMatch finish.nodes ic c :=
          ((rc.exprMatch.mono rt.nodesPrefix).mono rf.nodesPrefix).mono (NodesPrefix.push _ _)
        have hyes : ExprMatch finish.nodes it t :=
          (rt.exprMatch.mono rf.nodesPrefix).mono (NodesPrefix.push _ _)
        have hno : ExprMatch finish.nodes if_ f :=
          rf.exprMatch.mono (NodesPrefix.push _ _)
        have hctf : ic < s3.nodes.size ∧ it < s3.nodes.size ∧ if_ < s3.nodes.size :=
          ⟨((rc.exprMatch.mono rt.nodesPrefix).mono rf.nodesPrefix).root_lt,
            (rt.exprMatch.mono rf.nodesPrefix).root_lt, rf.exprMatch.root_lt⟩
        have hmatch : ExprMatch finish.nodes s3.nodes.size (.mux c t f) :=
          .mux hbound hnode hctf hcond hyes hno
        exact ⟨s3.nodes.size, finish,
          by simp [intern, hseen', rc.eq, rt.eq, rf.eq, finish, Build.add],
          rf.valid.add (by simp [Node.refs, hctf]) hmatch,
          ((rc.nodesPrefix.trans rt.nodesPrefix).trans rf.nodesPrefix).trans
            (NodesPrefix.push _ _), hmatch⟩
  | slice lo m a ih =>
      cases hseen : s.seen.get? (.slice lo m a) with
      | some root =>
        have hseen' : s.seen[FExpr.slice lo m a]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.slice lo m a]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := ih s valid
        let finish := (s1.add (.slice lo m a) (.slice lo m ia)).2
        have hbound : s1.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s1.nodes.size default = .slice lo m ia := by
          simp [finish, Build.add]
        have harg : ExprMatch finish.nodes ia a :=
          ra.exprMatch.mono (NodesPrefix.push _ _)
        have hmatch : ExprMatch finish.nodes s1.nodes.size (.slice lo m a) :=
          .slice hbound hnode ra.exprMatch.root_lt harg
        exact ⟨s1.nodes.size, finish,
          by simp [intern, hseen', ra.eq, finish, Build.add],
          ra.valid.add (by simp [Node.refs, ra.exprMatch.root_lt]) hmatch,
          ra.nodesPrefix.trans (NodesPrefix.push _ _), hmatch⟩
  | zext m a ih =>
      cases hseen : s.seen.get? (.zext m a) with
      | some root =>
        have hseen' : s.seen[FExpr.zext m a]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.zext m a]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := ih s valid
        let finish := (s1.add (.zext m a) (.zext m ia)).2
        have hbound : s1.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s1.nodes.size default = .zext m ia := by
          simp [finish, Build.add]
        have harg : ExprMatch finish.nodes ia a :=
          ra.exprMatch.mono (NodesPrefix.push _ _)
        have hmatch : ExprMatch finish.nodes s1.nodes.size (.zext m a) :=
          .zext hbound hnode ra.exprMatch.root_lt harg
        exact ⟨s1.nodes.size, finish,
          by simp [intern, hseen', ra.eq, finish, Build.add],
          ra.valid.add (by simp [Node.refs, ra.exprMatch.root_lt]) hmatch,
          ra.nodesPrefix.trans (NodesPrefix.push _ _), hmatch⟩
  | sext h m d a ih =>
      cases hseen : s.seen.get? (.sext h m d a) with
      | some root =>
        have hseen' : s.seen[FExpr.sext h m d a]? = some root := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        exact ⟨root, s, by simp [intern, hseen'], valid,
          NodesPrefix.refl _, valid.seen _ _ hseen⟩
      | none =>
        have hseen' : s.seen[FExpr.sext h m d a]? = none := by
          simpa [Std.HashMap.get?_eq_getElem?] using hseen
        obtain ⟨ia, s1, ra⟩ := ih s valid
        let finish := (s1.add (.sext h m d a) (.sext h m d ia)).2
        have hbound : s1.nodes.size < finish.nodes.size := by simp [finish, Build.add]
        have hnode : finish.nodes.getD s1.nodes.size default = .sext h m d ia := by
          simp [finish, Build.add]
        have harg : ExprMatch finish.nodes ia a :=
          ra.exprMatch.mono (NodesPrefix.push _ _)
        have hmatch : ExprMatch finish.nodes s1.nodes.size (.sext h m d a) :=
          .sext hbound hnode ra.exprMatch.root_lt harg
        exact ⟨s1.nodes.size, finish,
          by simp [intern, hseen', ra.eq, finish, Build.add],
          ra.valid.add (by simp [Node.refs, ra.exprMatch.root_lt]) hmatch,
          ra.nodesPrefix.trans (NodesPrefix.push _ _), hmatch⟩

theorem ActMatch.mono {small large : Array Node} {a : Act} {fa : FAct}
    (h : ActMatch small a fa) (pref : NodesPrefix small large) :
    ActMatch large a fa := by
  induction h with
  | skip => exact .skip
  | seq left right ihl ihr => exact .seq ihl ihr
  | ite cond yes no ihy ihn => exact .ite (cond.mono pref) ihy ihn
  | write value => exact .write (value.mono pref)
  | memWrite addr value => exact .memWrite (addr.mono pref) (value.mono pref)

structure LowerActResult (fa : FAct) (start : Build) (a : Act)
    (finish : Build) : Prop where
  eq : lowerAct fa start = (a, finish)
  valid : finish.Valid
  nodesPrefix : NodesPrefix start.nodes finish.nodes
  actMatch : ActMatch finish.nodes a fa

theorem lowerAct_complete (fa : FAct) (s : Build) (valid : s.Valid) :
    ∃ a finish, LowerActResult fa s a finish := by
  induction fa generalizing s with
  | skip => exact ⟨.skip, s, rfl, valid, NodesPrefix.refl _, .skip⟩
  | seq a b iha ihb =>
      obtain ⟨aa, s1, ra⟩ := iha s valid
      obtain ⟨ab, s2, rb⟩ := ihb s1 ra.valid
      exact ⟨.seq aa ab, s2, by simp [lowerAct, ra.eq, rb.eq], rb.valid,
        ra.nodesPrefix.trans rb.nodesPrefix,
        .seq (ra.actMatch.mono rb.nodesPrefix) rb.actMatch⟩
  | ite c t e iht ihe =>
      obtain ⟨ic, s1, rc⟩ := intern_complete c s valid
      obtain ⟨thenAct, s2, rt⟩ := iht s1 rc.valid
      obtain ⟨elseAct, s3, re⟩ := ihe s2 rt.valid
      exact ⟨.ite ic thenAct elseAct, s3,
        by simp [lowerAct, rc.eq, rt.eq, re.eq], re.valid,
        (rc.nodesPrefix.trans rt.nodesPrefix).trans re.nodesPrefix,
        .ite ((rc.exprMatch.mono rt.nodesPrefix).mono re.nodesPrefix)
          (rt.actMatch.mono re.nodesPrefix) re.actMatch⟩
  | write i v =>
      obtain ⟨iv, s1, rv⟩ := intern_complete v s valid
      exact ⟨.write i iv, s1, by simp [lowerAct, rv.eq], rv.valid,
        rv.nodesPrefix, .write rv.exprMatch⟩
  | memWrite base addr data =>
      obtain ⟨ia, s1, ra⟩ := intern_complete addr s valid
      obtain ⟨iv, s2, rv⟩ := intern_complete data s1 ra.valid
      exact ⟨.memWrite base ia iv, s2, by simp [lowerAct, ra.eq, rv.eq],
        rv.valid, ra.nodesPrefix.trans rv.nodesPrefix,
        .memWrite (ra.exprMatch.mono rv.nodesPrefix) rv.exprMatch⟩

structure LowerActsResult (facts : List FAct) (start : Build)
    (acts : List Act) (finish : Build) : Prop where
  eq : lowerActs facts start = (acts, finish)
  valid : finish.Valid
  nodesPrefix : NodesPrefix start.nodes finish.nodes
  actsMatch : ActsMatch finish.nodes acts facts

theorem lowerActs_complete (facts : List FAct) (s : Build) (valid : s.Valid) :
    ∃ acts finish, LowerActsResult facts s acts finish := by
  induction facts generalizing s with
  | nil => exact ⟨[], s, rfl, valid, NodesPrefix.refl _, .nil⟩
  | cons fa facts ih =>
      obtain ⟨a, s1, ra⟩ := lowerAct_complete fa s valid
      obtain ⟨acts, s2, rs⟩ := ih s1 ra.valid
      exact ⟨a :: acts, s2, by simp [lowerActs, ra.eq, rs.eq], rs.valid,
        ra.nodesPrefix.trans rs.nodesPrefix,
        .cons (ra.actMatch.mono rs.nodesPrefix) rs.actsMatch⟩

theorem lower_certificate (fd : FastDesign) : Certificate fd (lower fd) := by
  obtain ⟨acts, finish, result⟩ :=
    lowerActs_complete fd.acts.toList ({} : Build) Build.Valid.empty
  rw [show lower fd =
    { nodes := finish.nodes, acts := acts.toArray, slots := fd.slots } by
      simp [lower, result.eq]]
  exact ⟨result.valid.nodes, by simpa using result.actsMatch, rfl⟩

theorem prepare?_complete (fd : FastDesign) : (prepare? fd).isSome = true := by
  have hcheck := checkCertificate_complete (lower_certificate fd)
  unfold prepare?
  cases h : checkCertificate fd (lower fd) with
  | none => simp [h] at hcheck
  | some cert => simp [h]

theorem prepareSimulator?_complete {d : Loom.Hw.Design}
    (base : FastEval.VerifiedSimulator d) :
    (prepareSimulator? base).isSome = true := by
  have hprepare := prepare?_complete base.fast
  unfold prepareSimulator?
  cases h : prepare? base.fast with
  | none => simp [h] at hprepare
  | some dag => rfl

end Loom.Hw.DagEval
