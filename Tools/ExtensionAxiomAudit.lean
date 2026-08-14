-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Multiclock
import Tests.PrettyDsl
import Lean.Util.CollectAxioms

/-! Audit the declarations that exercise compositional pretty extensions at
both tutorial and production scale.  Expected closure: `propext`,
`Classical.choice`, and `Quot.sound` only. -/

#print axioms Tests.PrettyDsl.ExtendedIsland.extended
#print axioms Tests.PrettyDsl.ExtendedIsland.extended_with_memory
#print axioms Machines.Lnp64mini.Multiclock.authoredSystem
#print axioms Machines.Lnp64mini.Multiclock.authoredCore_eq_coreBody
#print axioms Machines.Lnp64mini.Multiclock.authoredCore_rtl_eq

private def auditedDeclarations : List Lean.Name :=
  [``Tests.PrettyDsl.ExtendedIsland.extended,
   ``Tests.PrettyDsl.ExtendedIsland.extended_with_memory,
   ``Machines.Lnp64mini.Multiclock.authoredSystem,
   ``Machines.Lnp64mini.Multiclock.authoredCore_eq_coreBody,
   ``Machines.Lnp64mini.Multiclock.authoredCore_rtl_eq]

private def permittedAxioms : List Lean.Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

-- Unlike the readable reports above, this command is an enforcing CI gate:
-- any expansion of the focused declarations' axiom closure fails elaboration.
run_cmd do
  for declaration in auditedDeclarations do
    let closure ← Lean.collectAxioms declaration
    let unexpected := closure.filter fun dependency =>
      !permittedAxioms.contains dependency
    unless unexpected.isEmpty do
      throwError "extension axiom audit failed for {declaration}: unexpected {unexpected.toList}"
