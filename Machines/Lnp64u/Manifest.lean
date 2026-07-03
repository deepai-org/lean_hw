import Machines.Lnp64u.State

/-!
# The reset-ROM manifest (L0)

Everything static about a configured LNP64-µ machine: per-domain priorities,
budgets, entry points, and initial capability tables; gate configurations;
the memory image. `initState` is the single boot function — the ISS, the
theorems' initial-state predicate, and (via refinement) the RTL reset all
mean exactly this.
-/

namespace Machines.Lnp64u

/-- Static configuration of one domain. -/
structure DomainCfg where
  /-- Scheduling priority; higher wins. Distinct across domains (WF). -/
  priority : Nat
  /-- Budget: `budgetQ` cycles per `periodP`-cycle period. -/
  budgetQ : Nat
  periodP : Nat
  /-- Reset program counter. -/
  entry : Addr
  /-- Root capabilities. These are the leaves of T2's authority closure. -/
  initCaps : Slot → Option CapKind

/-- The manifest: the machine's complete static configuration. -/
structure Manifest where
  doms  : DomainId → DomainCfg
  gates : GateId → GateConfig
  /-- The reset memory image. -/
  rom   : Addr → Loom.Word32

namespace Manifest

/-- Manifest well-formedness. `T7`'s schedulability premise (Σ Q/P ≤ 1) is
deliberately *not* here: it is a theorem hypothesis, not a boot requirement. -/
structure WF (m : Manifest) : Prop where
  /-- Priorities are distinct, so scheduling is deterministic. -/
  prio_inj : ∀ d d' : DomainId, (m.doms d).priority = (m.doms d').priority → d = d'
  /-- Periods are positive and budgets fit inside them. -/
  period_pos : ∀ d, 0 < (m.doms d).periodP
  budget_le : ∀ d, (m.doms d).budgetQ ≤ (m.doms d).periodP
  /-- Root memory capabilities satisfy W^X and lie within physical memory. -/
  caps_wx : ∀ d s base len perms, (m.doms d).initCaps s = some (.mem base len perms) →
    perms.wx = true ∧ base.toNat + len.toNat ≤ memWords

/-- Boot state of one domain. -/
def bootDom (cfg : DomainCfg) : DomainState where
  regs := fun _ => 0
  pc := cfg.entry
  caps := fun s => (cfg.initCaps s).map (fun k => { kind := k, lineage := none })
  slotGen := fun _ => genFirst
  lineage := fun _ => none
  regions := fun _ => none
  run := .running
  serving := none
  cause := 0
  budget := cfg.budgetQ

/-- The boot state: the one meaning of "reset". -/
def initState (m : Manifest) : MachineState where
  cycle := 0
  mem := m.rom
  doms := fun d => bootDom (m.doms d)
  gates := fun g => { config := m.gates g, act := none }
  mover := none
  inflight := none

end Manifest
end Machines.Lnp64u
