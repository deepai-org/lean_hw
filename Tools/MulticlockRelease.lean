-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Substrate.TwoClock
import Machines.Lnp64mini.Multiclock

/-!
# Publication-facing multiclock release bundle

This module is deliberately independent of the generated LNP64-u processor
release closure. The multiclock theorem can therefore be reviewed and have
its axiom closure checked at ordinary development cost; the combined release
imports this already-formed kernel object.
-/

namespace Loom.Release.Theorems

open Loom.Hw

/-- The complete portable multiclock release claim at both required scales. -/
structure CertifiedMulticlockRelease where
  small : System.CertifiedRealizedSystem
    Machines.Substrate.TwoClock.system Machines.Substrate.TwoClock.certified
  smallRTLSelected : small.rtlArtifact ∈ small.emissionArtifacts
  smallRTLBytes : small.rtlArtifact.text.toUTF8 = small.renderedUTF8
  smallRenderedBytes : small.renderedUTF8 = small.renderedVerilog.toUTF8
  production : System.CertifiedRealizedSystem
    Machines.Lnp64mini.Multiclock.system Machines.Lnp64mini.Multiclock.certified
  productionRTLSelected : production.rtlArtifact ∈ production.emissionArtifacts
  productionRTLBytes : production.rtlArtifact.text.toUTF8 = production.renderedUTF8
  productionRenderedBytes : production.renderedUTF8 = production.renderedVerilog.toUTF8

/-- The small released bytes and the production-scale instantiation are one
kernel-checked object. No Evidence target or physical macro is selected. -/
theorem verifiedMulticlockRelease : Nonempty CertifiedMulticlockRelease := by
  exact ⟨{
    small := Machines.Substrate.TwoClock.certifiedArtifact
    smallRTLSelected :=
      Machines.Substrate.TwoClock.certifiedArtifact.rtlArtifact_mem
    smallRTLBytes :=
      Machines.Substrate.TwoClock.certifiedArtifact.rtlArtifact_exact
    smallRenderedBytes := Machines.Substrate.TwoClock.certifiedArtifact_bytes
    production := Machines.Lnp64mini.Multiclock.certifiedArtifact
    productionRTLSelected :=
      Machines.Lnp64mini.Multiclock.certifiedArtifact.rtlArtifact_mem
    productionRTLBytes :=
      Machines.Lnp64mini.Multiclock.certifiedArtifact.rtlArtifact_exact
    productionRenderedBytes :=
      Machines.Lnp64mini.Multiclock.certifiedArtifact_bytes
  }⟩

end Loom.Release.Theorems
