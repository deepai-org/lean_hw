-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Hw.Demo
import Machines.Lnp64u.Theorems.RMC

/-! Kernel-checked finite premises for the exact emitted demo manifest. -/

namespace Machines.Lnp64u.Theorems.DemoWitness

open Machines.Lnp64u

set_option maxHeartbeats 0 in
/-- The manifest used by `lake exe emit lnp64u` is well formed. -/
theorem sys_wf : Demo.sysManifest.WF := by
  constructor
  · intro d d' h
    fin_cases d <;> fin_cases d' <;> simp [Demo.sysManifest] at h ⊢
  · intro d
    fin_cases d <;> decide
  · intro d
    fin_cases d <;> decide
  · intro d
    fin_cases d <;> decide
  · intro d s base len perms h
    fin_cases d <;> fin_cases s <;> simp [Demo.sysManifest] at h ⊢
    all_goals
      rcases h with ⟨rfl, rfl, rfl⟩
      decide

/-- The emitted demo manifest's parameters fit the hardware datapath. -/
theorem sys_fits : RMC.Fits Demo.sysManifest := by
  constructor <;> intro d <;> fin_cases d <;> decide

end Machines.Lnp64u.Theorems.DemoWitness
