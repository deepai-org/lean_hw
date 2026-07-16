-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ArtifactCert
import Loom.Emit.MicroVerilog.MatchesSemantics
import Loom.Release.Rope
import Loom.Release.SSA

/-!
# Parser-free release certificates

The concrete SSA witness has two independent kernel-checked views:

1. its structural renderer is equal, as logical lines, to the disk rope;
2. its structural elaborator produces a µVerilog module accepted by the
   generic compiler-result validator.

No property of the untrusted witness generator is assumed. The exact-byte
conclusion is obtained by congruence and therefore does not normalize the
full file string.
-/

namespace Loom.Release

open Loom.Emit.MicroVerilog

/-- Proof data needed to compare the elaborated concrete module with the
reference hardware compiler. -/
structure SSACert (design : Loom.Hw.Design) where
  module : Loom.Hw.ArtifactCert.ModuleCert design

/-- Check an arbitrary concrete program against the reference compiler. -/
def ssaMatches (design : Loom.Hw.Design) (program : SSA.Program)
    (cert : SSACert design) : Bool :=
  match program.elaborate with
  | some module => Loom.Hw.ArtifactCert.moduleMatches design module cert.module
  | none => false

/-- The parser-free structural certificate is sound for every witness, not
only witnesses produced by the release generator. -/
theorem ssaMatches_sound (design : Loom.Hw.Design) (program : SSA.Program)
    (cert : SSACert design) (h : ssaMatches design program cert = true) :
    ∃ module, program.elaborate = some module ∧
      module.Matches (Loom.Hw.Compile.compile design) := by
  unfold ssaMatches at h
  split at h
  · rename_i module helab
    exact ⟨module, helab,
      Loom.Hw.ArtifactCert.moduleMatches_sound design module cert.module h⟩
  · contradiction

/-- An accepted arbitrary concrete witness has exactly the transition-system
behavior of the reference compiler output. -/
theorem ssaMatches_behavior (design : Loom.Hw.Design) (program : SSA.Program)
    (cert : SSACert design) (h : ssaMatches design program cert = true) :
    ∃ module, program.elaborate = some module ∧
      module.toTSys = (Loom.Hw.Compile.compile design).toTSys := by
  obtain ⟨module, helab, hmatches⟩ := ssaMatches_sound design program cert h
  exact ⟨module, helab, hmatches.toTSys_eq⟩

/-- The publication-facing release boundary: exact rendered bytes plus equality
with the transition-system behavior of the proved reference compilation.
`renderedLines` is generated as a balanced tree of
named local render results. -/
theorem exactRenderingAndCompilation (design : Loom.Hw.Design)
    (program : SSA.Program) (disk : Rope (List String))
    (cert : SSACert design)
    (renderedLines : Rope (List String))
    (hrender : renderedLines = program.renderTree)
    (hdisk : renderedLines = disk)
    (hcert : ssaMatches design program cert = true) :
    program.renderTree.flattenBytes = disk.flattenBytes ∧
    ∃ module, program.elaborate = some module ∧
      module.toTSys = (Loom.Hw.Compile.compile design).toTSys := by
  constructor
  · exact Rope.flattenBytes_congr (hrender.symm.trans hdisk)
  · exact ssaMatches_behavior design program cert hcert

end Loom.Release
