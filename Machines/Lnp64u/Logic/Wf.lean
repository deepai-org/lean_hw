import Machines.Lnp64u.Logic.Defs

/-!
# The machine well-formedness invariant (L1, the workhorse)

The inductive invariant everything else strengthens (µLog DESIGN.md §Phase 1):
lineage bookkeeping is exact, parent pointers reach live capabilities,
cached authority (regions, Mover) is live and dominated by its backing
capability, gate records are consistent, and permissions respect W^X and
physical bounds. T2/T3/T8/T9 are corollaries or products with this.
-/

namespace Machines.Lnp64u

open Loom

/-- Per-domain bookkeeping well-formedness. -/
structure DomWf (ds : DomainState) : Prop where
  /-- Generations start at 1 and never read 0 (null is unconstructible). -/
  gen_pos : ∀ s : Slot, 1 ≤ (ds.slotGen s).toNat
  /-- A derived entry's cell exists. -/
  cell_backed : ∀ s e l, ds.caps s = some e → e.lineage = some l →
    (ds.lineage l).isSome
  /-- No two entries share a cell. -/
  ptr_inj : ∀ s s' e e' l, ds.caps s = some e → ds.caps s' = some e' →
    e.lineage = some l → e'.lineage = some l → s = s'
  /-- Every occupied cell is some entry's cell (with `cell_backed` and
  `ptr_inj`, cells ↔ derived entries is a bijection: T9's lineage ledger). -/
  cell_used : ∀ l, (ds.lineage l).isSome →
    ∃ s e, ds.caps s = some e ∧ e.lineage = some l
  /-- W^X on every live memory capability. -/
  wx : ∀ s base len p, ds.caps s = some ⟨.mem base len p, none⟩ ∨
       (∃ l, ds.caps s = some ⟨.mem base len p, some l⟩) → p.wx = true
  /-- Live memory capabilities lie within physical memory. -/
  bounds : ∀ s e base len p, ds.caps s = some e → e.kind = .mem base len p →
    base.toNat + len.toNat ≤ memWords

/-- Machine-wide well-formedness. -/
structure Wf (σ : MachineState) : Prop where
  doms : ∀ d, DomWf (σ.doms d)
  /-- Lineage chains point at live capabilities (maintained by reparent /
  splice / destroy-transitively; the property the revoke marking relies on). -/
  parent_live : ∀ d s p, σ.parentOf d s = some p → σ.liveRef p = true
  /-- Every region register's backing is live, and the region's authority
  is dominated by the backing capability (cached authority never exceeds
  nor outlives its source — T3/T8's core). -/
  region_backed : ∀ d r rg, (σ.doms d).regions r = some rg →
    ∃ e, ((σ.doms rg.backing.dom).liveCap rg.backing.slot rg.backing.gen) = some e ∧
         (CapKind.mem rg.base rg.len rg.perms).le e.kind
  /-- The Mover's capabilities are live and owned by the job's owner. -/
  mover_wf : ∀ job, σ.mover = some job →
    job.src.dom = job.owner ∧ job.dst.dom = job.owner ∧
    σ.liveRef job.src = true ∧ σ.liveRef job.dst = true
  /-- Gate records and domain marks agree: an activation exists iff its
  callee is serving that gate; a blocked domain is the caller of the gate
  it blocks on. -/
  gate_serving : ∀ g a, (σ.gates g).act = some a →
    ((σ.doms (σ.gates g).config.callee).serving = some g ∧
     (σ.doms a.caller).run = .blocked g ∧ 1 ≤ a.depth ∧ a.depth ≤ maxChainDepth)
  serving_gate : ∀ d g, (σ.doms d).serving = some g →
    ((σ.gates g).config.callee = d ∧ ((σ.gates g).act).isSome)
  blocked_gate : ∀ d g, (σ.doms d).run = .blocked g →
    ∃ a, (σ.gates g).act = some a ∧ a.caller = d
  /-- The in-flight instruction belongs to a running domain. -/
  inflight_running : ∀ fl, σ.inflight = some fl → (σ.doms fl.dom).run = .running

/-- The T9 lineage ledger: cells and derived entries balance exactly. A
consequence of `DomWf` (bijection), stated as the counting equation the
conservation theorem quotes. -/
def LedgerBalanced (σ : MachineState) : Prop :=
  ∀ d, cellCount (σ.doms d) = derivedCount (σ.doms d)

end Machines.Lnp64u
