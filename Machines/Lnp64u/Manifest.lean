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
  /-- Donation bound: cycles a gate activation called by this domain may
  consume before forced unwind (T6). -/
  maxDonation : Nat := 32
  /-- Reset program counter. -/
  entry : Addr
  /-- Root capabilities. These are the leaves of T2's authority closure. -/
  initCaps : Slot → Option CapKind
  /-- Boot-time region mappings: region register `r` caches the root
  capability in the named slot (fetch needs execute authority from cycle 0,
  so at least the code capability must boot mapped). -/
  initRegions : RegionId → Option Slot := fun _ => none

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
  /-- **Wrapping-timer periodicity (proof-forced 2026-07-04).** Every
  period divides `2 ^ 32`: the refill cadence `cycle % periodP = 0` is
  driven by the wrapping 32-bit cycle counter, and it stays periodic
  across the wrap only if `periodP ∣ 2 ^ 32` (otherwise the phase jumps at
  the wrap and a period boundary can be missed for up to `2·periodP`
  cycles). The same constraint real RTOS tick periods have against a
  free-running hardware timer. Since `hyperL` is the lcm of the periods,
  it inherits the divisibility (`hyperL_dvd_pow32`). -/
  period_dvd : ∀ d, (m.doms d).periodP ∣ 2 ^ 32
  /-- Root memory capabilities satisfy W^X and lie within physical memory. -/
  caps_wx : ∀ d s base len perms, (m.doms d).initCaps s = some (.mem base len perms) →
    perms.wx = true ∧ base.toNat + len.toNat ≤ memWords

/-- Boot state of domain `d`. -/
def bootDom (d : DomainId) (cfg : DomainCfg) : DomainState where
  regs := fun _ => 0
  pc := cfg.entry
  caps := fun s => (cfg.initCaps s).map (fun k => { kind := k, lineage := none })
  slotGen := fun _ => genFirst
  lineage := fun _ => none
  regions := fun r =>
    match cfg.initRegions r with
    | some s =>
        match cfg.initCaps s with
        | some (.mem base len perms) =>
            some { base := base, len := len, perms := perms
                   backing := ⟨d, s, genFirst⟩ }
        | _ => none
    | none => none
  run := .running
  serving := none
  cause := 0
  budget := cfg.budgetQ
  maxDonation := cfg.maxDonation

/-- The boot state: the one meaning of "reset". -/
def initState (m : Manifest) : MachineState where
  cycle := 0
  mem := m.rom
  doms := fun d => bootDom d (m.doms d)
  gates := fun g => { config := m.gates g, act := none }
  mover := none
  inflight := none

end Manifest
end Machines.Lnp64u
