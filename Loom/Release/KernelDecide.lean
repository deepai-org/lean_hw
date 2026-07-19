-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lean.Elab.Term
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.AuxLemma

/-!
# Metadata-free kernel decision proofs

Large generated release checks must be reduced by the kernel but should not
create a tactic information tree proportional to that reduction. This term
elaborator is the closed-term core of `by decide +kernel`: it asks the kernel
to check the standard `of_decide_eq_true` proof as a cached auxiliary lemma.
No evaluator, compiler result, or axiom is involved.
-/

open Lean Elab Term Meta

/-- Close a decidable, variable-free proposition by kernel reduction, without
emitting tactic metadata. -/
syntax (name := kernelDecide) "kernel_decide" : term

private partial def zetaLocalLets (expression : Expr) : TermElabM Expr := do
  let some fvar := expression.find? (·.isFVar) | return expression
  let localContext ← getLCtx
  let some declaration := localContext.find? fvar.fvarId!
    | return expression
  let some value := declaration.value? (allowNondep := true)
    | return expression
  zetaLocalLets (expression.replaceFVar fvar value)

@[term_elab kernelDecide]
def elabKernelDecide : TermElab := fun _ expected? => do
  let some expected := expected?
    | throwError "kernel_decide requires an expected proposition"
  let expected ← instantiateMVars expected
  let expected ← zetaLocalLets expected
  if expected.hasFVar || expected.hasMVar then
    throwError "kernel_decide requires a closed proposition"
  let proof ← mkDecideProof expected
  let levels := (collectLevelParams {} expected).params.toList
  let lemma ← withOptions (Elab.async.set · false) do
    mkAuxLemma levels expected proof (kind? := `_kernelDecide)
  pure (.const lemma (levels.map .param))
