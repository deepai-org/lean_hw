-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CompileCorrect
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Theorems.RMCResetDeclList

/-!
# Structural compiler well-formedness for the LNP64-µ release design

The large rule bodies are certified separately by generated, kernel-checked
declaration leaves. This file proves the stable machine-specific remainder:
unique state names and the exact `[0, 1, 2]` memory-port trace.
-/

namespace Machines.Lnp64u.Theorems.ReleaseWF

open Loom.Hw Loom.Hw.Compile

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem issueForMemoryTrace (m : Manifest) (domain : DomainId) :
    portTrace "mem" (Hw.issueFor m domain) = [] := by
  rfl

theorem issueFoldMemoryTrace (m : Manifest) (domains : List DomainId) :
    portTrace "mem"
      (domains.foldr (fun domain rest =>
        Loom.Hw.Act.ite (Hw.eligE m domain) (Hw.issueFor m domain) rest)
        .skip) = [] := by
  induction domains with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldr, portTrace, issueForMemoryTrace, ih,
        List.nil_append]

theorem refillMemoryTrace (m : Manifest) :
    portTrace "mem" (Hw.refillAct m) = [] := by rfl

theorem retireMemoryTrace :
    portTrace "mem" Hw.retireAct = [0] := by rfl

theorem rvInitMemoryTrace :
    portTrace "mem" Hw.rvInit = [] := by rfl

theorem rvStepMemoryTrace :
    portTrace "mem" Hw.rvStep = [] := by rfl

theorem moverMemoryTrace :
    portTrace "mem" Hw.moverAct = [1, 2] := by rfl

theorem tickMemoryTrace :
    portTrace "mem" Hw.tickAct = [] := by rfl

theorem coreMemoryTrace (m : Manifest) :
    portTrace "mem" (Hw.coreAct m) = [0] := by
  unfold Hw.coreAct
  simp only [portTrace]
  rw [issueFoldMemoryTrace]
  simp [retireMemoryTrace, rvInitMemoryTrace, rvStepMemoryTrace]

theorem designMemoryTrace (m : Manifest) :
    designTrace (Hw.core m) "mem" = [0, 1, 2] := by
  simp [Hw.core, designTrace, refillMemoryTrace, coreMemoryTrace,
    moverMemoryTrace, tickMemoryTrace]

/-- Generated declaration evidence is the only design-dependent input needed
to establish every compiler well-formedness premise for `Hw.core`. -/
theorem designWF_of_rules (m : Manifest)
    (rules : RulesDeclsOk (Hw.core m) (Hw.core m).rules) :
    DesignWF (Hw.core m) := by
  apply designWF_of_components (Hw.core m)
  · simpa [Hw.core] using RMC.names_nodup m
  · simp [Hw.core]
  · exact rules.all
  · intro mem member
    simp only [Hw.core, List.mem_singleton] at member
    subst mem
    change (designTrace (Hw.core m) "mem").Pairwise (fun a b => a < b)
    rw [designMemoryTrace]
    decide

end Machines.Lnp64u.Theorems.ReleaseWF
