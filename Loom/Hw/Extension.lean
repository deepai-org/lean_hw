-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Chan
import Loom.Hw.CompileCorrect
import Loom.Hw.ReadsOk

/-!
# Incremental design-extension certificates

Pretty `system` declarations may append a small migration fragment to a large,
already checked `Design`, then add generated channel endpoints.  Re-running the
whole read and compiler check on that result makes proof construction scale with
the old machine instead of the new source.  This file gives that boundary a
compositional certificate: the base is checked once, while each extension checks
only its new declarations, rules, memory traces, and endpoint adapters.

This is proof infrastructure, not a second user-facing design type.
-/

namespace Loom.Hw

open Compile

/-- Read declarations in `body`, but resolve them against `scope`. -/
def Design.readsOkInB (scope body : Design) : Bool :=
  let sites := body.readSites
  let badRegs := sites.1.filter fun (n, w) =>
    !((scope.regs.any fun r => r.name = n && r.width = w) ||
      (scope.inputs.any fun i => i.name = n && i.width = w))
  let badMems := sites.2.filter fun (m, dw) =>
    !(scope.mems.any fun md => md.name = m && md.dataWidth = dw)
  badRegs.isEmpty && badMems.isEmpty

def Design.regReadDeclaredB (scope : Design) (site : String × Nat) : Bool :=
  (scope.regs.any fun reg => reg.name = site.1 && reg.width = site.2) ||
    (scope.inputs.any fun input =>
      input.name = site.1 && input.width = site.2)

def Design.RegReadDeclared (scope : Design) (site : String × Nat) : Prop :=
  scope.regReadDeclaredB site = true

def Design.memReadDeclaredB (scope : Design) (site : String × Nat) : Bool :=
  scope.mems.any fun memory =>
    memory.name = site.1 && memory.dataWidth = site.2

def Design.MemReadDeclared (scope : Design) (site : String × Nat) : Prop :=
  scope.memReadDeclaredB site = true

/-- Proposition-level form used by extension proofs. -/
structure Design.ReadsValidIn (scope body : Design) : Prop where
  regs : ∀ site ∈ body.readSites.1, scope.RegReadDeclared site
  mems : ∀ site ∈ body.readSites.2, scope.MemReadDeclared site

private theorem not_not_true_iff (value : Bool) :
    (¬ (!value) = true) ↔ value = true := by
  cases value <;> simp

private theorem foldRuleReads_fst (rules : List Rule)
    (acc : List (String × Nat) × List (String × Nat)) (site) :
    site ∈ (rules.foldl (fun acc rule =>
      let sites := rule.body.readSites
      (acc.1 ++ sites.1, acc.2 ++ sites.2)) acc).1 ↔
      site ∈ acc.1 ∨ ∃ rule ∈ rules, site ∈ rule.body.readSites.1 := by
  induction rules generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.mem_append, List.mem_cons]
      aesop

private theorem foldRuleReads_snd (rules : List Rule)
    (acc : List (String × Nat) × List (String × Nat)) (site) :
    site ∈ (rules.foldl (fun acc rule =>
      let sites := rule.body.readSites
      (acc.1 ++ sites.1, acc.2 ++ sites.2)) acc).2 ↔
      site ∈ acc.2 ∨ ∃ rule ∈ rules, site ∈ rule.body.readSites.2 := by
  induction rules generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.mem_append, List.mem_cons]
      aesop

private theorem foldOutputReads_fst (outputs : List CombOutput)
    (acc : List (String × Nat) × List (String × Nat)) (site) :
    site ∈ (outputs.foldl (fun acc output =>
      let sites := output.value.readSites
      (acc.1 ++ sites.1, acc.2 ++ sites.2)) acc).1 ↔
      site ∈ acc.1 ∨ ∃ output ∈ outputs, site ∈ output.value.readSites.1 := by
  induction outputs generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.mem_append, List.mem_cons]
      aesop

private theorem foldOutputReads_snd (outputs : List CombOutput)
    (acc : List (String × Nat) × List (String × Nat)) (site) :
    site ∈ (outputs.foldl (fun acc output =>
      let sites := output.value.readSites
      (acc.1 ++ sites.1, acc.2 ++ sites.2)) acc).2 ↔
      site ∈ acc.2 ∨ ∃ output ∈ outputs, site ∈ output.value.readSites.2 := by
  induction outputs generalizing acc with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.mem_append, List.mem_cons]
      aesop

theorem Design.mem_readSites_fst_iff (d : Design) (site) :
    site ∈ d.readSites.1 ↔
      (∃ rule ∈ d.rules, site ∈ rule.body.readSites.1) ∨
      ∃ output ∈ d.combOutputs, site ∈ output.value.readSites.1 := by
  unfold Design.readSites
  rw [foldOutputReads_fst, foldRuleReads_fst]
  simp

theorem Design.mem_readSites_snd_iff (d : Design) (site) :
    site ∈ d.readSites.2 ↔
      (∃ rule ∈ d.rules, site ∈ rule.body.readSites.2) ∨
      ∃ output ∈ d.combOutputs, site ∈ output.value.readSites.2 := by
  unfold Design.readSites
  rw [foldOutputReads_snd, foldRuleReads_snd]
  simp

private def sitesReadOkInB (scope : Design)
    (sites : List (String × Nat) × List (String × Nat)) : Bool :=
  sites.1.all scope.regReadDeclaredB && sites.2.all scope.memReadDeclaredB

def Expr.readsOkInB (scope : Design) : {width : Nat} → Expr width → Bool
  | _, .lit _ => true
  | width, .reg _ name => scope.regReadDeclaredB (name, width)
  | width, .memRead _ memory address =>
      scope.memReadDeclaredB (memory, width) && address.readsOkInB scope
  | _, .and left right | _, .or left right | _, .xor left right
  | _, .add left right | _, .sub left right | _, .mul left right
  | _, .udiv left right | _, .urem left right | _, .shl left right
  | _, .shr left right | _, .eq left right | _, .ult left right
  | _, .slt left right => left.readsOkInB scope && right.readsOkInB scope
  | _, .not value | _, .slice value _ _ | _, .zext value _
  | _, .sext value _ => value.readsOkInB scope
  | _, .mux condition yes no =>
      condition.readsOkInB scope && yes.readsOkInB scope &&
        no.readsOkInB scope

def Act.readsOkInB (scope : Design) : Act → Bool
  | .skip => true
  | .seq left right => left.readsOkInB scope && right.readsOkInB scope
  | .ite condition yes no =>
      condition.readsOkInB scope && yes.readsOkInB scope &&
        no.readsOkInB scope
  | .write _ _ value | .writeSlice _ _ _ _ _ value =>
      value.readsOkInB scope
  | .memWrite _ _ _ _ address value =>
      address.readsOkInB scope && value.readsOkInB scope

structure Act.ReadsValidIn (scope : Design) (action : Act) : Prop where
  regs : ∀ site ∈ action.readSites.1, scope.RegReadDeclared site
  mems : ∀ site ∈ action.readSites.2, scope.MemReadDeclared site

private theorem Expr.readsOkInB_eq_sites (scope : Design) {width : Nat}
    (expression : Expr width) :
    expression.readsOkInB scope = sitesReadOkInB scope expression.readSites := by
  induction expression <;>
    simp [Expr.readsOkInB, Expr.readSites, sitesReadOkInB, *,
      List.all_append, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

private theorem Act.readsOkInB_eq_sites (scope : Design) (action : Act) :
    action.readsOkInB scope = sitesReadOkInB scope action.readSites := by
  induction action <;>
    simp [Act.readsOkInB, Act.readSites, sitesReadOkInB,
      Expr.readsOkInB_eq_sites, *, List.all_append, Bool.and_assoc,
      Bool.and_left_comm, Bool.and_comm]

theorem Act.readsOkInB_iff (scope : Design) (action : Act) :
    action.readsOkInB scope = true ↔ Act.ReadsValidIn scope action := by
  rw [Act.readsOkInB_eq_sites]
  simp only [sitesReadOkInB, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨regs, mems⟩
    exact ⟨regs, mems⟩
  · rintro ⟨regs, mems⟩
    exact ⟨regs, mems⟩

def CombOutput.readsOkInB (scope : Design) (output : CombOutput) : Bool :=
  output.value.readsOkInB scope

structure CombOutput.ReadsValidIn (scope : Design)
    (output : CombOutput) : Prop where
  regs : ∀ site ∈ output.value.readSites.1, scope.RegReadDeclared site
  mems : ∀ site ∈ output.value.readSites.2, scope.MemReadDeclared site

theorem CombOutput.readsOkInB_iff (scope : Design) (output : CombOutput) :
    output.readsOkInB scope = true ↔
      CombOutput.ReadsValidIn scope output := by
  rw [CombOutput.readsOkInB, Expr.readsOkInB_eq_sites]
  simp only [sitesReadOkInB, Bool.and_eq_true,
    List.all_eq_true]
  constructor
  · rintro ⟨regs, mems⟩
    exact ⟨regs, mems⟩
  · rintro ⟨regs, mems⟩
    exact ⟨regs, mems⟩

theorem Design.ReadsValidIn.ofComponents {scope body : Design}
    (rules : ∀ rule ∈ body.rules, Act.ReadsValidIn scope rule.body)
    (outputs : ∀ output ∈ body.combOutputs,
      CombOutput.ReadsValidIn scope output) :
    Design.ReadsValidIn scope body := by
  constructor
  · intro site member
    rw [Design.mem_readSites_fst_iff] at member
    rcases member with ⟨rule, ruleMember, read⟩ |
        ⟨output, outputMember, read⟩
    · exact (rules rule ruleMember).regs site read
    · exact (outputs output outputMember).regs site read
  · intro site member
    rw [Design.mem_readSites_snd_iff] at member
    rcases member with ⟨rule, ruleMember, read⟩ |
        ⟨output, outputMember, read⟩
    · exact (rules rule ruleMember).mems site read
    · exact (outputs output outputMember).mems site read

/-- Rule/output-local read checker.  Unlike `readsOkB`, it never constructs
one whole-design read-site list, so large DAG-shaped machines can certify each
rule independently without an allocation spike. -/
def Design.readsOkInComponentsB (scope body : Design) : Bool :=
  body.rules.all (fun rule => rule.body.readsOkInB scope) &&
  body.combOutputs.all (fun output => output.readsOkInB scope)

theorem Design.readsOkInComponentsB_iff (scope body : Design) :
    scope.readsOkInComponentsB body = true ↔
      Design.ReadsValidIn scope body := by
  simp only [readsOkInComponentsB, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨rules, outputs⟩
    constructor
    · intro site member
      rw [mem_readSites_fst_iff] at member
      rcases member with ⟨rule, ruleMember, read⟩ |
          ⟨output, outputMember, read⟩
      · exact ((Act.readsOkInB_iff scope rule.body).mp
          (rules rule ruleMember)).regs site read
      · exact ((CombOutput.readsOkInB_iff scope output).mp
          (outputs output outputMember)).regs site read
    · intro site member
      rw [mem_readSites_snd_iff] at member
      rcases member with ⟨rule, ruleMember, read⟩ |
          ⟨output, outputMember, read⟩
      · exact ((Act.readsOkInB_iff scope rule.body).mp
          (rules rule ruleMember)).mems site read
      · exact ((CombOutput.readsOkInB_iff scope output).mp
          (outputs output outputMember)).mems site read
  · rintro ⟨regs, mems⟩
    constructor
    · intro rule ruleMember
      apply (Act.readsOkInB_iff scope rule.body).mpr
      exact ⟨fun site read => regs site ((mem_readSites_fst_iff body site).mpr
          (Or.inl ⟨rule, ruleMember, read⟩)),
        fun site read => mems site ((mem_readSites_snd_iff body site).mpr
          (Or.inl ⟨rule, ruleMember, read⟩))⟩
    · intro output outputMember
      apply (CombOutput.readsOkInB_iff scope output).mpr
      exact ⟨fun site read => regs site ((mem_readSites_fst_iff body site).mpr
          (Or.inr ⟨output, outputMember, read⟩)),
        fun site read => mems site ((mem_readSites_snd_iff body site).mpr
          (Or.inr ⟨output, outputMember, read⟩))⟩

theorem Design.readsOkInB_iff (scope body : Design) :
    scope.readsOkInB body = true ↔ Design.ReadsValidIn scope body := by
  simp only [readsOkInB, Bool.and_eq_true, List.isEmpty_iff,
    List.filter_eq_nil_iff]
  constructor
  · rintro ⟨hregs, hmems⟩
    constructor
    · intro site member
      exact (not_not_true_iff _).mp (hregs site member)
    · intro site member
      exact (not_not_true_iff _).mp (hmems site member)
  · rintro ⟨hregs, hmems⟩
    constructor
    · intro site member
      exact (not_not_true_iff _).mpr (hregs site member)
    · intro site member
      exact (not_not_true_iff _).mpr (hmems site member)

@[simp] theorem Design.readsOkInB_self (d : Design) :
    d.readsOkInB d = d.readsOkB := by
  rfl

/-- The already-paid proof obligations for a base design.  Large legacy
designs name one value of this structure; pretty-authored designs get one from
their declaration command. -/
class ExtensionBaseReady (base : Design) : Prop where
  names :
    (base.names.eraseDups.length == base.names.length) = true
  reads : Design.ReadsValidIn base base
  compiler : Compile.DesignWF base

/-- Proof that `adapted` is exactly `added` after zero or more stock endpoint
adapters.  Making this an inductive closure (rather than an arbitrary prefix
relation) prevents callers from disguising unrelated declarations as generated
endpoint plumbing. -/
inductive ExtensionAdaptation (added : Design) : Design → Prop where
  | refl : ExtensionAdaptation added added
  | withSource {width : Nat} {adapted : Design}
      (valid : ExtensionAdaptation added adapted) (channel : Chan width) :
      ExtensionAdaptation added (channel.withSource adapted)
  | withSink {width : Nat} {adapted : Design}
      (valid : ExtensionAdaptation added adapted) (channel : Chan width) :
      ExtensionAdaptation added (channel.withSink adapted)

theorem ExtensionAdaptation.reg_mem {added adapted : Design}
    (valid : ExtensionAdaptation added adapted) :
    ∀ reg ∈ added.regs, reg ∈ adapted.regs := by
  induction valid with
  | refl => simp
  | withSource valid channel ih =>
      intro reg member
      simp [Chan.withSource, ih reg member]
  | withSink valid channel ih =>
      intro reg member
      simp [Chan.withSink, ih reg member]

/-- Structural relationship between the old design, the endpoint-adapted new
body, and the final endpoint-adapted scope.  The list relations deliberately
mention only names and rule/comb-output membership; no action tree is reduced.
-/
structure ExtensionShape (base addedBody scope : Design) : Prop where
  regNames :
    (scope.regs.map (·.name)).Perm
      ((base.regs.map (·.name)) ++ (addedBody.regs.map (·.name)))
  memNames :
    (scope.mems.map (·.name)).Perm
      ((base.mems.map (·.name)) ++ (addedBody.mems.map (·.name)))
  inputNames :
    (scope.inputs.map (·.name)).Perm
      ((base.inputs.map (·.name)) ++ (addedBody.inputs.map (·.name)))
  rules : scope.rules.Perm (base.rules ++ addedBody.rules)
  combOutputs : scope.combOutputs.Perm (base.combOutputs ++ addedBody.combOutputs)
  traces : ∀ memory,
    Compile.designTrace scope memory =
      Compile.designTrace base memory ++ Compile.designTrace addedBody memory
  baseRegs : ∀ reg ∈ base.regs, reg ∈ scope.regs
  baseMems : ∀ memory ∈ base.mems, memory ∈ scope.mems
  scopeMems : ∀ memory ∈ scope.mems,
    memory ∈ base.mems ∨ memory ∈ addedBody.mems
  baseRegDecls : ∀ site, base.RegReadDeclared site → scope.RegReadDeclared site
  baseMemDecls : ∀ site, base.MemReadDeclared site → scope.MemReadDeclared site
  readRegs : ∀ site ∈ scope.readSites.1,
    site ∈ base.readSites.1 ∨ site ∈ addedBody.readSites.1
  readMems : ∀ site ∈ scope.readSites.2,
    site ∈ base.readSites.2 ∨ site ∈ addedBody.readSites.2

private theorem readSites_fst_of_layout {base addedBody scope : Design}
    (rules : scope.rules.Perm (base.rules ++ addedBody.rules))
    (outputs : scope.combOutputs.Perm
      (base.combOutputs ++ addedBody.combOutputs)) :
    ∀ site ∈ scope.readSites.1,
      site ∈ base.readSites.1 ∨ site ∈ addedBody.readSites.1 := by
  intro site member
  rw [Design.mem_readSites_fst_iff] at member
  rcases member with ⟨rule, ruleMember, read⟩ | ⟨output, outputMember, read⟩
  · have : rule ∈ base.rules ∨ rule ∈ addedBody.rules := by
      have := rules.mem_iff.mp ruleMember
      simpa only [List.mem_append] using this
    rcases this with old | new
    · exact Or.inl ((Design.mem_readSites_fst_iff base site).mpr
        (Or.inl ⟨rule, old, read⟩))
    · exact Or.inr ((Design.mem_readSites_fst_iff addedBody site).mpr
        (Or.inl ⟨rule, new, read⟩))
  · have : output ∈ base.combOutputs ∨ output ∈ addedBody.combOutputs := by
      have := outputs.mem_iff.mp outputMember
      simpa only [List.mem_append] using this
    rcases this with old | new
    · exact Or.inl ((Design.mem_readSites_fst_iff base site).mpr
        (Or.inr ⟨output, old, read⟩))
    · exact Or.inr ((Design.mem_readSites_fst_iff addedBody site).mpr
        (Or.inr ⟨output, new, read⟩))

private theorem readSites_snd_of_layout {base addedBody scope : Design}
    (rules : scope.rules.Perm (base.rules ++ addedBody.rules))
    (outputs : scope.combOutputs.Perm
      (base.combOutputs ++ addedBody.combOutputs)) :
    ∀ site ∈ scope.readSites.2,
      site ∈ base.readSites.2 ∨ site ∈ addedBody.readSites.2 := by
  intro site member
  rw [Design.mem_readSites_snd_iff] at member
  rcases member with ⟨rule, ruleMember, read⟩ | ⟨output, outputMember, read⟩
  · have : rule ∈ base.rules ∨ rule ∈ addedBody.rules := by
      have := rules.mem_iff.mp ruleMember
      simpa only [List.mem_append] using this
    rcases this with old | new
    · exact Or.inl ((Design.mem_readSites_snd_iff base site).mpr
        (Or.inl ⟨rule, old, read⟩))
    · exact Or.inr ((Design.mem_readSites_snd_iff addedBody site).mpr
        (Or.inl ⟨rule, new, read⟩))
  · have : output ∈ base.combOutputs ∨ output ∈ addedBody.combOutputs := by
      have := outputs.mem_iff.mp outputMember
      simpa only [List.mem_append] using this
    rcases this with old | new
    · exact Or.inl ((Design.mem_readSites_snd_iff base site).mpr
        (Or.inr ⟨output, old, read⟩))
    · exact Or.inr ((Design.mem_readSites_snd_iff addedBody site).mpr
        (Or.inr ⟨output, new, read⟩))

/-- Construct the shape from list-level composition facts. -/
theorem ExtensionShape.ofLayout {base addedBody scope : Design}
    (regNames : (scope.regs.map (·.name)).Perm
      ((base.regs.map (·.name)) ++ (addedBody.regs.map (·.name))))
    (memNames : (scope.mems.map (·.name)).Perm
      ((base.mems.map (·.name)) ++ (addedBody.mems.map (·.name))))
    (inputNames : (scope.inputs.map (·.name)).Perm
      ((base.inputs.map (·.name)) ++ (addedBody.inputs.map (·.name))))
    (rules : scope.rules.Perm (base.rules ++ addedBody.rules))
    (combOutputs : scope.combOutputs.Perm
      (base.combOutputs ++ addedBody.combOutputs))
    (traces : ∀ memory, Compile.designTrace scope memory =
      Compile.designTrace base memory ++ Compile.designTrace addedBody memory)
    (baseRegs : ∀ reg ∈ base.regs, reg ∈ scope.regs)
    (baseMems : ∀ memory ∈ base.mems, memory ∈ scope.mems)
    (scopeMems : ∀ memory ∈ scope.mems,
      memory ∈ base.mems ∨ memory ∈ addedBody.mems)
    (baseRegDecls : ∀ site,
      base.RegReadDeclared site → scope.RegReadDeclared site)
    (baseMemDecls : ∀ site,
      base.MemReadDeclared site → scope.MemReadDeclared site) :
    ExtensionShape base addedBody scope :=
  ⟨regNames, memNames, inputNames, rules, combOutputs, traces,
    baseRegs, baseMems, scopeMems, baseRegDecls, baseMemDecls,
    readSites_fst_of_layout rules combOutputs,
    readSites_snd_of_layout rules combOutputs⟩

@[simp] theorem Compile.designTrace_par (left right : Design) (memory : String) :
    Compile.designTrace (left.par right) memory =
      Compile.designTrace left memory ++ Compile.designTrace right memory := by
  simp [Compile.designTrace, Design.par, List.flatMap_append]

@[simp] theorem Compile.designTrace_withSource {width : Nat} (channel : Chan width)
    (design : Design) (memory : String) :
    Compile.designTrace (channel.withSource design) memory =
      Compile.designTrace design memory := by
  simp [Compile.designTrace, Chan.withSource, Compile.portTrace]

@[simp] theorem Compile.designTrace_withSink {width : Nat} (channel : Chan width)
    (design : Design) (memory : String) :
    Compile.designTrace (channel.withSink design) memory =
      Compile.designTrace design memory := by
  simp [Compile.designTrace, Chan.withSink, Compile.portTrace]

/-- Initial shape before endpoint adaptation. -/
theorem ExtensionShape.par (base added : Design) :
    ExtensionShape base added (base.par added) := by
  apply ExtensionShape.ofLayout
  · simp [Design.par]
  · simp [Design.par]
  · simp [Design.par]
  · simp [Design.par]
  · simp [Design.par]
  · exact Compile.designTrace_par base added
  · intro reg member
    simp [Design.par, member]
  · intro memory member
    simp [Design.par, member]
  · intro memory member
    simpa [Design.par] using member
  · intro site declared
    simp only [Design.RegReadDeclared, Design.regReadDeclaredB,
      Design.par, List.any_append]
    simp only [Design.RegReadDeclared, Design.regReadDeclaredB] at declared
    generalize (base.regs.any fun reg =>
      reg.name = site.1 && reg.width = site.2) = baseRegs at declared ⊢
    generalize (added.regs.any fun reg =>
      reg.name = site.1 && reg.width = site.2) = addedRegs at ⊢
    generalize (base.inputs.any fun input =>
      input.name = site.1 && input.width = site.2) = baseInputs at declared ⊢
    generalize (added.inputs.any fun input =>
      input.name = site.1 && input.width = site.2) = addedInputs at ⊢
    cases baseRegs <;> cases addedRegs <;> cases baseInputs <;>
      cases addedInputs <;> simp_all
  · intro site declared
    simp only [Design.MemReadDeclared, Design.memReadDeclaredB,
      Design.par, List.any_append]
    simp only [Design.MemReadDeclared, Design.memReadDeclaredB] at declared
    simp [declared]

private theorem perm_front_through_left {α : Type} (front left right : List α)
    {middle : List α} (permutation : middle.Perm (left ++ right)) :
    (front ++ middle).Perm (left ++ (front ++ right)) :=
  (permutation.append_left front).trans
    (List.perm_append_comm_assoc front left right)

private theorem regReadDeclared_with_front
    (base extended : Design) (site : String × Nat)
    (valid : base.RegReadDeclared site)
    (regFront inputFront : Bool)
    (hregs : (extended.regs.any fun reg =>
      reg.name = site.1 && reg.width = site.2) =
        (regFront || (base.regs.any fun reg =>
          reg.name = site.1 && reg.width = site.2)))
    (hinputs : (extended.inputs.any fun input =>
      input.name = site.1 && input.width = site.2) =
        (inputFront || (base.inputs.any fun input =>
          input.name = site.1 && input.width = site.2))) :
    extended.RegReadDeclared site := by
  simp only [Design.RegReadDeclared, Design.regReadDeclaredB] at valid ⊢
  rw [hregs, hinputs]
  generalize (base.regs.any fun reg =>
    reg.name = site.1 && reg.width = site.2) = oldRegs at valid ⊢
  generalize (base.inputs.any fun input =>
    input.name = site.1 && input.width = site.2) = oldInputs at valid ⊢
  cases regFront <;> cases inputFront <;> cases oldRegs <;>
    cases oldInputs <;> simp_all

/-- Adding a generated source endpoint to both the final scope and the local
body preserves extension shape. -/
theorem ExtensionShape.withSource {width : Nat} {base addedBody scope : Design}
    (shape : ExtensionShape base addedBody scope) (channel : Chan width) :
    ExtensionShape base (channel.withSource addedBody)
      (channel.withSource scope) := by
  apply ExtensionShape.ofLayout
  · simpa [Chan.withSource, List.map_append] using
      perm_front_through_left
        [channel.sourceValidName, channel.sourcePayloadName]
        (base.regs.map (·.name)) (addedBody.regs.map (·.name)) shape.regNames
  · simpa [Chan.withSource] using shape.memNames
  · simpa [Chan.withSource, List.map_append] using
      perm_front_through_left
        [channel.sourceReadyName, channel.sourceAcceptedName]
        (base.inputs.map (·.name)) (addedBody.inputs.map (·.name)) shape.inputNames
  · simpa [Chan.withSource] using
      perm_front_through_left
        [⟨channel.stem ++ "source_maintenance",
          .ite channel.sourceAccepted
            (.write 1 channel.sourceValidName (.lit 0)) .skip⟩]
        base.rules addedBody.rules shape.rules
  · simpa [Chan.withSource] using shape.combOutputs
  · intro memory
    simp [shape.traces]
  · intro reg member
    simp [Chan.withSource, shape.baseRegs reg member]
  · intro memory member
    simpa [Chan.withSource] using shape.baseMems memory member
  · intro memory member
    simpa [Chan.withSource] using shape.scopeMems memory member
  · intro site declared
    apply regReadDeclared_with_front scope (channel.withSource scope) site
      (shape.baseRegDecls site declared)
      ((decide (channel.sourceValidName = site.1) && decide (1 = site.2)) ||
       (decide (channel.sourcePayloadName = site.1) && decide (width = site.2)))
      ((decide (channel.sourceReadyName = site.1) && decide (1 = site.2)) ||
       (decide (channel.sourceAcceptedName = site.1) && decide (1 = site.2)))
    · simp [Chan.withSource, Bool.or_assoc]
    · simp [Chan.withSource, Bool.or_assoc]
  · intro site declared
    simpa [Design.MemReadDeclared, Chan.withSource] using shape.baseMemDecls site declared

/-- Adding a generated sink endpoint to both sides preserves extension shape. -/
theorem ExtensionShape.withSink {width : Nat} {base addedBody scope : Design}
    (shape : ExtensionShape base addedBody scope) (channel : Chan width) :
    ExtensionShape base (channel.withSink addedBody)
      (channel.withSink scope) := by
  apply ExtensionShape.ofLayout
  · simpa [Chan.withSink, List.map_append] using
      perm_front_through_left [channel.sinkPopName]
        (base.regs.map (·.name)) (addedBody.regs.map (·.name)) shape.regNames
  · simpa [Chan.withSink] using shape.memNames
  · simpa [Chan.withSink, List.map_append] using
      perm_front_through_left
        [channel.sinkValidName, channel.sinkPayloadName]
        (base.inputs.map (·.name)) (addedBody.inputs.map (·.name)) shape.inputNames
  · simpa [Chan.withSink] using
      perm_front_through_left
        [⟨channel.stem ++ "sink_maintenance",
          .write 1 channel.sinkPopName (.lit 0)⟩]
        base.rules addedBody.rules shape.rules
  · simpa [Chan.withSink] using shape.combOutputs
  · intro memory
    simp [shape.traces]
  · intro reg member
    simp [Chan.withSink, shape.baseRegs reg member]
  · intro memory member
    simpa [Chan.withSink] using shape.baseMems memory member
  · intro memory member
    simpa [Chan.withSink] using shape.scopeMems memory member
  · intro site declared
    apply regReadDeclared_with_front scope (channel.withSink scope) site
      (shape.baseRegDecls site declared)
      (decide (channel.sinkPopName = site.1) && decide (1 = site.2))
      ((decide (channel.sinkValidName = site.1) && decide (1 = site.2)) ||
       (decide (channel.sinkPayloadName = site.1) && decide (width = site.2)))
    · simp [Chan.withSink]
    · simp [Chan.withSink, Bool.or_assoc]
  · intro site declared
    simpa [Design.MemReadDeclared, Chan.withSink] using shape.baseMemDecls site declared

/-- The bounded obligations introduced by one extension.  The common
no-memory path inspects only `addedBody` (the new fragment plus generated
endpoint rules).  The general path additionally checks old/new memory-port
ordering for memories the fragment writes. -/
structure ExtensionLocalReady (base addedBody scope : Design) : Prop where
  addedNames :
    (addedBody.names.eraseDups.length == addedBody.names.length) = true
  namesDisjoint :
    base.names.all (fun name => !addedBody.names.contains name) = true
  ruleNamesDisjoint :
    (base.rules.map (·.name)).all
      (fun name => !(addedBody.rules.map (·.name)).contains name) = true
  regNames : (addedBody.regs.map (·.name)).Nodup
  memNames : (addedBody.mems.map (·.name)).Nodup
  regNamesDisjoint : List.Disjoint
    (base.regs.map (·.name)) (addedBody.regs.map (·.name))
  memNamesDisjoint : List.Disjoint
    (base.mems.map (·.name)) (addedBody.mems.map (·.name))
  reads : scope.readsOkInB addedBody = true
  writes : Compile.RulesDeclsOk scope addedBody.rules
  localPorts : ∀ memory ∈ scope.mems,
    (Compile.designTrace addedBody memory.name).Pairwise (fun a b => a < b)
  crossPorts : ∀ memory ∈ base.mems,
    ∀ oldPort ∈ Compile.designTrace base memory.name,
    ∀ newPort ∈ Compile.designTrace addedBody memory.name,
      oldPort < newPort

/-- A bounded proof that a local rule list contains no memory writes.  This is
the common extension case (including generated channel endpoints), and avoids
even enumerating the base design's memory traces. -/
def RulesNoMemWrites : List Rule → Prop
  | [] => True
  | rule :: rest => rule.body.memWrites = [] ∧ RulesNoMemWrites rest

theorem RulesNoMemWrites.all {rules : List Rule}
    (valid : RulesNoMemWrites rules) :
    ∀ rule ∈ rules, rule.body.memWrites = [] := by
  induction rules with
  | nil => simp
  | cons head tail ih =>
      intro rule member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid.1
      · exact ih valid.2 rule member

theorem designTrace_eq_nil_of_rulesNoMemWrites (design : Design)
    (valid : RulesNoMemWrites design.rules) (memory : String) :
    Compile.designTrace design memory = [] := by
  unfold Compile.designTrace
  apply List.flatMap_eq_nil_iff.mpr
  intro rule member
  apply Compile.portTrace_eq_nil_of_not_memWrites
  simp [valid.all rule member]

/-- Construct the local certificate for the usual extension that adds no
memory writes.  Every supplied check is fragment-local; in particular, no
base action or memory trace is reduced. -/
theorem ExtensionLocalReady.ofNoMemoryWrites
    {base addedBody scope : Design}
    (addedNames :
      (addedBody.names.eraseDups.length == addedBody.names.length) = true)
    (namesDisjoint :
      base.names.all (fun name => !addedBody.names.contains name) = true)
    (ruleNamesDisjoint :
      (base.rules.map (·.name)).all
        (fun name => !(addedBody.rules.map (·.name)).contains name) = true)
    (regNames : (addedBody.regs.map (·.name)).Nodup)
    (memNames : (addedBody.mems.map (·.name)).Nodup)
    (regNamesDisjoint : List.Disjoint
      (base.regs.map (·.name)) (addedBody.regs.map (·.name)))
    (memNamesDisjoint : List.Disjoint
      (base.mems.map (·.name)) (addedBody.mems.map (·.name)))
    (reads : scope.readsOkInB addedBody = true)
    (writes : Compile.RulesDeclsOk scope addedBody.rules)
    (noMemoryWrites : RulesNoMemWrites addedBody.rules) :
    ExtensionLocalReady base addedBody scope := by
  refine ⟨addedNames, namesDisjoint, ruleNamesDisjoint, regNames, memNames,
    regNamesDisjoint, memNamesDisjoint, reads, writes, ?_, ?_⟩
  · intro memory declared
    rw [designTrace_eq_nil_of_rulesNoMemWrites addedBody noMemoryWrites]
    simp
  · intro memory baseDeclared oldPort oldMember newPort newMember
    rw [designTrace_eq_nil_of_rulesNoMemWrites addedBody noMemoryWrites] at newMember
    simp at newMember

def stringNodupB : List String → Bool
  | [] => true
  | name :: rest => !rest.contains name && stringNodupB rest

theorem stringNodupB_eq_true_iff (names : List String) :
    stringNodupB names = true ↔ names.Nodup := by
  induction names with
  | nil => simp [stringNodupB]
  | cons head tail ih =>
      simp [stringNodupB, ih]

def stringDisjointB (left right : List String) : Bool :=
  left.all fun name => !right.contains name

theorem stringDisjointB_eq_true_iff (left right : List String) :
    stringDisjointB left right = true ↔ List.Disjoint left right := by
  simp [stringDisjointB, List.disjoint_left]

def RulesNoMemWritesB (rules : List Rule) : Bool :=
  rules.all fun rule => rule.body.memWrites.isEmpty

theorem RulesNoMemWritesB_eq_true_iff (rules : List Rule) :
    RulesNoMemWritesB rules = true ↔ RulesNoMemWrites rules := by
  induction rules with
  | nil => simp [RulesNoMemWritesB, RulesNoMemWrites]
  | cons head tail ih =>
      simp only [RulesNoMemWritesB, List.all_cons, Bool.and_eq_true,
        RulesNoMemWrites]
      change (tail.all fun rule => rule.body.memWrites.isEmpty) = true ↔
        RulesNoMemWrites tail at ih
      simp [List.isEmpty_iff, ih]

theorem rulesDeclsOk_iff_all (scope : Design) (rules : List Rule) :
    Compile.RulesDeclsOk scope rules ↔
      rules.all (fun rule => Compile.actionDeclsOk scope rule.body) = true := by
  induction rules with
  | nil => simp [Compile.RulesDeclsOk]
  | cons head tail ih =>
      simp only [Compile.RulesDeclsOk, List.all_cons, Bool.and_eq_true]
      rw [ih]

def extensionLocalPortsOkB (scope addedBody : Design) : Bool :=
  scope.mems.all fun memory =>
    decide ((Compile.designTrace addedBody memory.name).Pairwise (fun a b => a < b))

theorem extensionLocalPortsOkB_sound {scope addedBody : Design}
    (valid : extensionLocalPortsOkB scope addedBody = true) :
    ∀ memory ∈ scope.mems,
      (Compile.designTrace addedBody memory.name).Pairwise (fun a b => a < b) := by
  intro memory member
  have checked := List.all_eq_true.mp valid memory member
  exact of_decide_eq_true checked

def extensionCrossPortsOkB (base addedBody : Design) : Bool :=
  base.mems.all fun memory =>
    -- Inspect the fragment first.  A fragment that does not write this base
    -- memory returns `true` without reducing that memory's base trace.
    (Compile.designTrace addedBody memory.name).all fun newPort =>
      (Compile.designTrace base memory.name).all fun oldPort =>
        decide (oldPort < newPort)

theorem extensionCrossPortsOkB_sound {base addedBody : Design}
    (valid : extensionCrossPortsOkB base addedBody = true) :
    ∀ memory ∈ base.mems,
      ∀ oldPort ∈ Compile.designTrace base memory.name,
      ∀ newPort ∈ Compile.designTrace addedBody memory.name,
        oldPort < newPort := by
  intro memory memoryMember oldPort oldMember newPort newMember
  have memoryChecked := List.all_eq_true.mp valid memory memoryMember
  have newChecked := List.all_eq_true.mp memoryChecked newPort newMember
  have oldChecked := List.all_eq_true.mp newChecked oldPort oldMember
  exact of_decide_eq_true oldChecked

/-- General generated constructor.  Unlike the common no-memory fast path,
this checks the new fragment's local port ordering and its ordering after old
base writes.  It is selected only when the fragment actually writes memory. -/
theorem ExtensionLocalReady.ofChecks
    {base addedBody scope : Design}
    (addedNames :
      (addedBody.names.eraseDups.length == addedBody.names.length) = true)
    (namesDisjoint :
      base.names.all (fun name => !addedBody.names.contains name) = true)
    (ruleNamesDisjoint :
      (base.rules.map (·.name)).all
        (fun name => !(addedBody.rules.map (·.name)).contains name) = true)
    (regNames : stringNodupB (addedBody.regs.map (·.name)) = true)
    (memNames : stringNodupB (addedBody.mems.map (·.name)) = true)
    (regNamesDisjoint : stringDisjointB
      (base.regs.map (·.name)) (addedBody.regs.map (·.name)) = true)
    (memNamesDisjoint : stringDisjointB
      (base.mems.map (·.name)) (addedBody.mems.map (·.name)) = true)
    (reads : scope.readsOkInB addedBody = true)
    (writes : addedBody.rules.all
      (fun rule => Compile.actionDeclsOk scope rule.body) = true)
    (localPorts : extensionLocalPortsOkB scope addedBody = true)
    (crossPorts : extensionCrossPortsOkB base addedBody = true) :
    ExtensionLocalReady base addedBody scope :=
  ⟨addedNames, namesDisjoint, ruleNamesDisjoint,
    (stringNodupB_eq_true_iff _).mp regNames,
    (stringNodupB_eq_true_iff _).mp memNames,
    (stringDisjointB_eq_true_iff _ _).mp regNamesDisjoint,
    (stringDisjointB_eq_true_iff _ _).mp memNamesDisjoint,
    reads, (rulesDeclsOk_iff_all scope addedBody.rules).mpr writes,
    extensionLocalPortsOkB_sound localPorts,
    extensionCrossPortsOkB_sound crossPorts⟩

/-- Boolean-fronted constructor used by generated syntax.  These checks are
small and executable, while this theorem turns them into the semantic local
facts used by `ofComponents`. -/
theorem ExtensionLocalReady.ofChecksNoMemoryWrites
    {base addedBody scope : Design}
    (addedNames :
      (addedBody.names.eraseDups.length == addedBody.names.length) = true)
    (namesDisjoint :
      base.names.all (fun name => !addedBody.names.contains name) = true)
    (ruleNamesDisjoint :
      (base.rules.map (·.name)).all
        (fun name => !(addedBody.rules.map (·.name)).contains name) = true)
    (regNames : stringNodupB (addedBody.regs.map (·.name)) = true)
    (memNames : stringNodupB (addedBody.mems.map (·.name)) = true)
    (regNamesDisjoint : stringDisjointB
      (base.regs.map (·.name)) (addedBody.regs.map (·.name)) = true)
    (memNamesDisjoint : stringDisjointB
      (base.mems.map (·.name)) (addedBody.mems.map (·.name)) = true)
    (reads : scope.readsOkInB addedBody = true)
    (writes : addedBody.rules.all
      (fun rule => Compile.actionDeclsOk scope rule.body) = true)
    (noMemoryWrites : RulesNoMemWritesB addedBody.rules = true) :
    ExtensionLocalReady base addedBody scope :=
  ExtensionLocalReady.ofNoMemoryWrites addedNames namesDisjoint
    ruleNamesDisjoint
    ((stringNodupB_eq_true_iff _).mp regNames)
    ((stringNodupB_eq_true_iff _).mp memNames)
    ((stringDisjointB_eq_true_iff _ _).mp regNamesDisjoint)
    ((stringDisjointB_eq_true_iff _ _).mp memNamesDisjoint)
    reads ((rulesDeclsOk_iff_all scope addedBody.rules).mpr writes)
    ((RulesNoMemWritesB_eq_true_iff _).mp noMemoryWrites)

/-- Audit-clean proof object consumed by `extendDesign`.  `readsDeclared` and
`compiler` are consequences supplied by the compositional constructor below;
they are retained here so downstream callers can use the ordinary Loom facts.
-/
structure ExtensionCertificate (base added addedBody scope : Design) : Prop where
  adaptation : ExtensionAdaptation added addedBody
  namespaces : base.parOkB addedBody = true
  readsDeclared : scope.readsOkB = true
  compiler : Compile.DesignWF scope

private theorem ExtensionShape.readsValid
    {base addedBody scope : Design}
    (shape : ExtensionShape base addedBody scope)
    (baseReady : ExtensionBaseReady base)
    (addedReady : ExtensionLocalReady base addedBody scope) :
    Design.ReadsValidIn scope scope := by
  have baseValid : Design.ReadsValidIn base base := baseReady.reads
  have addedValid : Design.ReadsValidIn scope addedBody :=
    (Design.readsOkInB_iff scope addedBody).mp addedReady.reads
  constructor
  · intro site member
    rcases shape.readRegs site member with old | new
    · exact shape.baseRegDecls site (baseValid.regs site old)
    · exact addedValid.regs site new
  · intro site member
    rcases shape.readMems site member with old | new
    · exact shape.baseMemDecls site (baseValid.mems site old)
    · exact addedValid.mems site new

private theorem ExtensionShape.compilerWF
    {base addedBody scope : Design}
    (shape : ExtensionShape base addedBody scope)
    (baseReady : ExtensionBaseReady base)
    (addedReady : ExtensionLocalReady base addedBody scope) :
    Compile.DesignWF scope := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply shape.regNames.nodup_iff.mpr
    exact List.nodup_append.mpr
      ⟨baseReady.compiler.regNames, addedReady.regNames,
        fun left leftMember right rightMember equal =>
          (List.disjoint_left.mp addedReady.regNamesDisjoint
            leftMember (equal ▸ rightMember))⟩
  · apply shape.memNames.nodup_iff.mpr
    exact List.nodup_append.mpr
      ⟨baseReady.compiler.memNames, addedReady.memNames,
        fun left leftMember right rightMember equal =>
          (List.disjoint_left.mp addedReady.memNamesDisjoint
            leftMember (equal ▸ rightMember))⟩
  · intro rule member name width write
    have classified : rule ∈ base.rules ∨ rule ∈ addedBody.rules := by
      have : rule ∈ base.rules ++ addedBody.rules :=
        shape.rules.mem_iff.mp member
      simpa only [List.mem_append] using this
    rcases classified with old | new
    · obtain ⟨reg, declared, rfl, rfl⟩ :=
        baseReady.compiler.regWrites rule old name width write
      exact ⟨reg, shape.baseRegs reg declared, rfl, rfl⟩
    · exact addedReady.writes.regWrites new write
  · intro rule member name write
    have classified : rule ∈ base.rules ∨ rule ∈ addedBody.rules := by
      have : rule ∈ base.rules ++ addedBody.rules :=
        shape.rules.mem_iff.mp member
      simpa only [List.mem_append] using this
    rcases classified with old | new
    · obtain ⟨memory, declared, rfl⟩ :=
        baseReady.compiler.memWrites rule old name write
      exact ⟨memory, shape.baseMems memory declared, rfl⟩
    · exact addedReady.writes.memWrites new write
  · intro memory declared
    rcases shape.scopeMems memory declared with oldMemory | newMemory
    · refine ⟨?_, ?_⟩
      · intro rule member
        have classified : rule ∈ base.rules ∨ rule ∈ addedBody.rules := by
          have : rule ∈ base.rules ++ addedBody.rules :=
            shape.rules.mem_iff.mp member
          simpa only [List.mem_append] using this
        rcases classified with oldRule | newRule
        · exact (baseReady.compiler.memory memory oldMemory).widths rule oldRule
        · exact addedReady.writes.widths newRule declared
      · rw [shape.traces]
        exact List.pairwise_append.mpr
          ⟨(baseReady.compiler.memory memory oldMemory).ports,
            addedReady.localPorts memory declared,
            addedReady.crossPorts memory oldMemory⟩
    · refine ⟨?_, ?_⟩
      · intro rule member
        have classified : rule ∈ base.rules ∨ rule ∈ addedBody.rules := by
          have : rule ∈ base.rules ++ addedBody.rules :=
            shape.rules.mem_iff.mp member
          simpa only [List.mem_append] using this
        rcases classified with oldRule | newRule
        · apply Compile.widthsOk_of_not_memWrites memory rule.body
          intro writes
          obtain ⟨baseMemory, baseDeclared, sameName⟩ :=
            baseReady.compiler.memWrites rule oldRule memory.name writes
          have disjoint := addedReady.memNamesDisjoint
          rw [List.disjoint_left] at disjoint
          exact disjoint
            (List.mem_map.mpr ⟨baseMemory, baseDeclared, sameName⟩)
            (List.mem_map.mpr ⟨memory, newMemory, rfl⟩)
        · exact addedReady.writes.widths newRule declared
      · rw [shape.traces]
        have baseTraceEmpty : Compile.designTrace base memory.name = [] := by
          unfold Compile.designTrace
          apply List.flatMap_eq_nil_iff.mpr
          intro rule oldRule
          apply Compile.portTrace_eq_nil_of_not_memWrites
          intro writes
          obtain ⟨baseMemory, baseDeclared, sameName⟩ :=
            baseReady.compiler.memWrites rule oldRule memory.name writes
          have disjoint := addedReady.memNamesDisjoint
          rw [List.disjoint_left] at disjoint
          exact disjoint
            (List.mem_map.mpr ⟨baseMemory, baseDeclared, sameName⟩)
            (List.mem_map.mpr ⟨memory, newMemory, rfl⟩)
        rw [baseTraceEmpty, List.nil_append]
        exact addedReady.localPorts memory declared

/-- Build the public certificate from named base readiness and bounded local
facts.  No proof in this constructor reduces the base action tree. -/
theorem ExtensionCertificate.ofComponents
    {base added addedBody scope : Design}
    (baseReady : ExtensionBaseReady base)
    (adaptation : ExtensionAdaptation added addedBody)
    (shape : ExtensionShape base addedBody scope)
    (addedReady : ExtensionLocalReady base addedBody scope) :
    ExtensionCertificate base added addedBody scope := by
  refine ⟨adaptation, ?_, ?_, shape.compilerWF baseReady addedReady⟩
  · simp only [Design.parOkB, Bool.and_eq_true]
    exact ⟨⟨⟨addedReady.namesDisjoint, baseReady.names⟩,
      addedReady.addedNames⟩, addedReady.ruleNamesDisjoint⟩
  · exact (Design.readsOkInB_iff scope scope).mpr
      (shape.readsValid baseReady addedReady)

end Loom.Hw
