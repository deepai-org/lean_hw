-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import GeneratedRelease.Acc8.SemanticRelease
import GeneratedRelease.Lnp64u.SemanticRelease
import Machines.Lnp64u.Theorems.T2
import Machines.Lnp64u.Theorems.T8
import Machines.Lnp64u.Theorems.T9
import Machines.Lnp64mini.Harness
import Machines.Substrate.S0Blinky

/-!
# Final release theorem

This module is built only by the release pipeline, after both generated
artifact witnesses have been kernel-checked. `verifiedReleases` is the one
publication-facing theorem binding both shipped byte streams to concrete SSA
programs, complete declarative denotations, and proved processor refinements.
-/

open Loom Loom.Hw Loom.Release

namespace Loom.Release.Theorems

/-- The fixed Acc8 publication artifact proposition. -/
abbrev Acc8ReleaseArtifact := VerifiedSymbolicArtifact
      (Machines.Acc8.machine
        (Machines.Acc8.loadProg Machines.Acc8.golden))
      (Machines.Acc8.Core.design
        (Machines.Acc8.loadProg Machines.Acc8.golden))
      Loom.GeneratedRelease.Acc8.program
      Loom.GeneratedRelease.Acc8.diskTree
      Loom.GeneratedRelease.Acc8.indexedWireTree
      Loom.GeneratedRelease.Acc8.wireTable
      Loom.GeneratedRelease.Acc8.registerRootTree
      Loom.GeneratedRelease.Acc8.memoryRoots
      Loom.GeneratedRelease.Acc8.outputIndexTree

/-- The fixed LNP64-µ publication artifact proposition. -/
abbrev Lnp64uReleaseArtifact := VerifiedSymbolicArtifact
      (Machines.Lnp64u.machine Machines.Lnp64u.Demo.sysManifest)
      (Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest)
      Loom.GeneratedRelease.Lnp64u.program
      Loom.GeneratedRelease.Lnp64u.diskTree
      Loom.GeneratedRelease.Lnp64u.indexedWireTree
      Loom.GeneratedRelease.Lnp64u.wireTable
      Loom.GeneratedRelease.Lnp64u.registerRootTree
      Loom.GeneratedRelease.Lnp64u.memoryRoots
      Loom.GeneratedRelease.Lnp64u.outputIndexTree

/-- The single publication-facing claim for both exact shipped artifacts.

Besides exact bytes, complete concrete-SSA denotation, and ISS refinement,
the bundle states representative headline security invariants directly over
the compiled system denoted by the LNP64-µ bytes: authority confinement,
machine-wide W^X, lineage-ledger conservation, and budget boundedness. -/
structure VerifiedReleases where
  acc8 : Acc8ReleaseArtifact
  lnp64u : Lnp64uReleaseArtifact
  authorityConfinement :
    (Compile.compile
      (Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest)).toTSys.Invariant
      (fun state =>
        let iss := lnp64u.refinement.abs state
        Machines.Lnp64u.Wf iss ∧
          Machines.Lnp64u.AuthorityConfined
            Machines.Lnp64u.Demo.sysManifest iss)
  wxSafety :
    (Compile.compile
      (Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest)).toTSys.Invariant
      (fun state =>
        let iss := lnp64u.refinement.abs state
        (∀ d s base len p l,
          (iss.doms d).caps s = some ⟨.mem base len p, l⟩ → p.wx = true) ∧
        (∀ d r region, (iss.doms d).regions r = some region →
          region.perms.wx = true))
  ledgerConservation :
    (Compile.compile
      (Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest)).toTSys.Invariant
      (fun state => Machines.Lnp64u.LedgerBalanced
        (lnp64u.refinement.abs state))
  budgetBounded :
    (Compile.compile
      (Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest)).toTSys.Invariant
      (fun state => ∀ d,
        ((lnp64u.refinement.abs state).doms d).budget ≤
          (Machines.Lnp64u.Demo.sysManifest.doms d).budgetQ)

/-- Both shipped Verilog artifacts have exact byte witnesses whose concrete
SSA denotations refine their proved processor models and carry the named
LNP64-µ security invariants to the denoted compiled system. -/
theorem verifiedReleases : Nonempty VerifiedReleases := by
  obtain ⟨acc8⟩ := Loom.GeneratedRelease.Acc8.verifiedRelease
  obtain ⟨lnp64u⟩ := Loom.GeneratedRelease.Lnp64u.verifiedRelease
  exact ⟨{
    acc8
    lnp64u
    authorityConfinement := lnp64u.invariant_pullback
      (Machines.Lnp64u.Theorems.T2.authority_confined
        Machines.Lnp64u.Demo.sysManifest
        Machines.Lnp64u.Theorems.DemoWitness.sys_wf)
    wxSafety := lnp64u.invariant_pullback
      (Machines.Lnp64u.Theorems.T8.wx_machine_wide
        Machines.Lnp64u.Demo.sysManifest
        Machines.Lnp64u.Theorems.DemoWitness.sys_wf)
    ledgerConservation := lnp64u.invariant_pullback
      (Machines.Lnp64u.Theorems.T9.ledger_balanced
        Machines.Lnp64u.Demo.sysManifest
        Machines.Lnp64u.Theorems.DemoWitness.sys_wf)
    budgetBounded := lnp64u.invariant_pullback
      (Machines.Lnp64u.Theorems.T9.budget_bounded
        Machines.Lnp64u.Demo.sysManifest
        Machines.Lnp64u.Theorems.DemoWitness.sys_wf)
  }⟩

/-- The two publication claims in one kernel object: exact released UTF-8
bytes, and a Design-derived certified simulator connected directly to the
proved compiler for arbitrary inputs, states, and finite run lengths.  The
two concrete packages prevent the generic API from being merely schematic. -/
structure FormalSubstance where
  releases : VerifiedReleases
  dagCompilerRun : ∀ {d : Design} (sim : DagEval.VerifiedSimulator d),
    Compile.DesignWF d → ∀ (n : Nat) (ιs : Nat → InEnv) (fs : FastSt)
      (state : Loom.Emit.MicroVerilog.St),
      DagEval.CompiledAgree d fs state →
      DagEval.CompiledAgree d (sim.runOpen ιs n fs)
        ((Compile.compile d).runOpen ιs n state)
  dagPreparation : ∀ {d : Design} (base : FastEval.VerifiedSimulator d),
    (DagEval.prepareSimulator? base).isSome = true
  smallDesign : CertifiedDesign Machines.Substrate.S0Blinky.design
  productionDesign : CertifiedDesign Machines.Lnp64mini.design

/-- Publication-facing closure joining the byte theorem, generic simulator
theorems, preparation completeness, and two real certified Designs. -/
theorem formalSubstance : Nonempty FormalSubstance := by
  obtain ⟨releases⟩ := verifiedReleases
  exact ⟨{
    releases
    dagCompilerRun := fun sim wf n ιs fs state agree =>
      sim.compiledRunOpen_eq wf n ιs fs state agree
    dagPreparation := DagEval.prepareSimulator?_complete
    smallDesign := Machines.Substrate.S0Blinky.certified
    productionDesign := Machines.Lnp64mini.certified
  }⟩

end Loom.Release.Theorems
