-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGrant

/-!
# R-MC mem_grant framing

Unchanged-domain and gate faces for the fully selected grant action.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000

private theorem grantExplicit_read_notin_other (e t x : DomainId)
    (hxe : x ≠ e) (hxt : x ≠ t) (NS : Slot) (NL : LineageId) :
    ∀ q ∈ domReadNames x, q ∉ (grantExplicit e t NS NL).regWrites := by
  fin_cases e <;> fin_cases t <;> fin_cases x <;>
    first
      | exact absurd rfl hxe
      | exact absurd rfl hxt
      | native_decide +revert

/-- A selected grant leaves every domain other than issuer and target
unchanged. -/
theorem absDom_grantExplicit_other (σ acc : Loom.Hw.St)
    (e t x : DomainId) (hxe : x ≠ e) (hxt : x ≠ t)
    (NS : Slot) (NL : LineageId) :
    Hw.absDom ((grantExplicit e t NS NL).run σ acc) x =
      Hw.absDom acc x := by
  apply absDom_congr
  intro q hq
  exact frame (grantExplicit_read_notin_other e t x hxe hxt NS NL q hq)
    σ acc

private theorem grantExplicit_gate_notin (e t : DomainId)
    (NS : Slot) (NL : LineageId) (g : GateId) :
    ∀ q ∈ gateReadNames g, q ∉ (grantExplicit e t NS NL).regWrites := by
  fin_cases e <;> fin_cases t <;> fin_cases g <;>
    native_decide +revert

/-- A selected grant does not alter any gate record. -/
theorem absGate_grantExplicit (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (g : GateId) :
    Hw.absGate ((grantExplicit e t NS NL).run σ acc) g =
      Hw.absGate acc g := by
  apply absGate_congr
  intro q hq
  exact frame (grantExplicit_gate_notin e t NS NL g q hq) σ acc

end Machines.Lnp64u.Theorems.RMC
