-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Logic.AcyclicWfa

/-!
# R-MC reachable-state well-formedness bridge

A compact opaque projection of the combined `Wf ∧ Acyclic` invariant. Keeping
the state generic here prevents clients from normalizing a large concrete
abstraction merely to project its `Wf` component.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u

/-- Every reachable specification state is well-formed. -/
theorem reachable_wf (m : Manifest) (hwf : m.WF) (τ : MachineState)
    (hτ : (machine m).Reachable τ) : Wf τ :=
  (Machines.Lnp64u.wfa_invariant m hwf τ hτ).1

/-- An in-flight domain cannot be the blocked caller of an active gate. -/
theorem Wf.inflight_ne_gateCaller {τ : MachineState} (h : Wf τ)
    (fl : InFlight) (hfl : τ.inflight = some fl) (gid : GateId)
    (act : Activation) (hact : (τ.gates gid).act = some act) :
    fl.dom ≠ act.caller := by
  have hrun : (τ.doms fl.dom).run = .running := h.inflight_running fl hfl
  have hblocked : (τ.doms act.caller).run = .blocked gid :=
    (h.gate_serving gid act hact).2.1
  intro heq
  rw [heq, hblocked] at hrun
  contradiction

end Machines.Lnp64u.Theorems.RMC
