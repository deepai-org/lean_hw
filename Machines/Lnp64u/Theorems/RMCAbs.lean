import Machines.Lnp64u.Theorems.RMCReset
import Machines.Lnp64u.Theorems.RMCEnc

/-!
# R-MC support: `abs` at reset, field by field

The cheap fields of `abs_reset` (`cycle`, `mem`, `mover`, `inflight`, and
the four gates), each landed sorry-free from `reset_lookup` arms. The
domain field (`absDom_reset`, 548 further lookup arms) is the remaining
bulk — see `scripts/gen_rmc_reset_tab.py` for the generated table and the
declList optimization it needs before it is CI-affordable.

Arm indices come from the `regDecls` layout (module docstring of the
generator); a wrong index fails to typecheck.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom.Hw Machines.Lnp64u.Hw

/-! ## The landed lookup arms (globals + gate blocks) -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_cycle (m : Manifest) :
    (Hw.core m).reset.regs "cycle" 32 = m.initState.cycle :=
  reset_lookup m 632 (by omega)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_movV (m : Manifest) :
    (Hw.core m).reset.regs "mov_v" 1
      = (if m.initState.mover.isSome then 1 else 0) :=
  reset_lookup m 620 (by omega)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_ifV (m : Manifest) :
    (Hw.core m).reset.regs "if_v" 1
      = (if m.initState.inflight.isSome then 1 else 0) :=
  reset_lookup m 628 (by omega)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_gcallee (m : Manifest) : ∀ (g : GateId),
    (Hw.core m).reset.regs (Hw.gcallee g) 2
      = BitVec.ofNat 2 (m.initState.gates g).config.callee.val
  | ⟨0, _⟩ => reset_lookup m 548 (by omega)
  | ⟨1, _⟩ => reset_lookup m 566 (by omega)
  | ⟨2, _⟩ => reset_lookup m 584 (by omega)
  | ⟨3, _⟩ => reset_lookup m 602 (by omega)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_gentry (m : Manifest) : ∀ (g : GateId),
    (Hw.core m).reset.regs (Hw.gentry g) 12
      = (m.initState.gates g).config.entry
  | ⟨0, _⟩ => reset_lookup m 549 (by omega)
  | ⟨1, _⟩ => reset_lookup m 567 (by omega)
  | ⟨2, _⟩ => reset_lookup m 585 (by omega)
  | ⟨3, _⟩ => reset_lookup m 603 (by omega)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_gactV (m : Manifest) : ∀ (g : GateId),
    (Hw.core m).reset.regs (Hw.gactV g) 1
      = (if (m.initState.gates g).act.isSome then 1 else 0)
  | ⟨0, _⟩ => reset_lookup m 550 (by omega)
  | ⟨1, _⟩ => reset_lookup m 568 (by omega)
  | ⟨2, _⟩ => reset_lookup m 586 (by omega)
  | ⟨3, _⟩ => reset_lookup m 604 (by omega)

/-! ## `abs` fields at reset -/

set_option maxRecDepth 400000 in
set_option maxHeartbeats 16000000 in
/-- The abstracted cycle counter boots at the spec's boot cycle (0). -/
theorem abs_cycle_reset (m : Manifest) :
    (Hw.abs (Hw.core m).reset).cycle = m.initState.cycle := by
  show (Hw.core m).reset.regs "cycle" 32 = m.initState.cycle
  rw [reset_cycle]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 16000000 in
/-- The abstracted RAM boots at the boot image. -/
theorem abs_mem_reset (m : Manifest) :
    (Hw.abs (Hw.core m).reset).mem = m.initState.mem := by
  funext a
  show (Hw.core m).reset.mems "mem" a.toNat 32 = m.initState.mem a
  rw [reset_mem]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

set_option maxRecDepth 400000 in
set_option maxHeartbeats 16000000 in
/-- The Mover boots idle. -/
theorem abs_mover_reset (m : Manifest) :
    (Hw.abs (Hw.core m).reset).mover = m.initState.mover := by
  show Hw.absMover (Hw.core m).reset = m.initState.mover
  rw [Hw.absMover, reset_movV]
  simp [Manifest.initState]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 16000000 in
/-- The core boots with no instruction in flight. -/
theorem abs_inflight_reset (m : Manifest) :
    (Hw.abs (Hw.core m).reset).inflight = m.initState.inflight := by
  show Hw.absInflight (Hw.core m).reset = m.initState.inflight
  rw [Hw.absInflight, reset_ifV]
  simp [Manifest.initState]

set_option maxRecDepth 400000 in
set_option maxHeartbeats 16000000 in
/-- Gate registers boot at the manifest configuration with no activation. -/
theorem absGate_reset (m : Manifest) (g : GateId) :
    Hw.absGate (Hw.core m).reset g = m.initState.gates g := by
  rw [Hw.absGate, reset_gcallee, reset_gentry, reset_gactV]
  simp only [Manifest.initState, Option.isSome_none, Bool.false_eq_true,
    if_false, finOfBv_ofNat]
  rfl

end Machines.Lnp64u.Theorems.RMC
