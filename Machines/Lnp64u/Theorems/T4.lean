import Machines.Lnp64u.Logic.Wf
import Machines.Lnp64u.Logic.GateStep

/-!
# T4 — Integrity / frame theorem

Exactly four influence channels between domains at µ scale — granted
memory, the gate reply, Mover writes into granted destinations, the status
word — plus the scrub equalities: activation entry registers ∈ {args,
zeros}; caller resumption = saved file plus `rd := reply`.
-/

namespace Machines.Lnp64u.Theorems.T4

open Machines.Lnp64u Loom

/-- **Scrub equality (entry).** When a gate activation begins — callee `c`
transitions from not-serving to serving `g` in one cycle — the callee's
register file holds the argument handle in `r1` and zero everywhere else,
and its PC is the gate's entry point. -/
theorem activation_entry_scrubbed (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (c : DomainId) (g : GateId)
    (hpre : (σ.doms c).serving = none)
    (hpost : ((step m σ).doms c).serving = some g) :
    (∀ r : RegId, r ≠ (1 : Fin numRegs) →
       ((step m σ).doms c).reg r = 0) ∧
    ((step m σ).doms c).pc = (σ.gates g).config.entry := by
  have hwfσ : Wf σ := (Machines.Lnp64u.wfa_invariant m hwf σ hreach).1
  exact (step_touch m σ hwfσ c).1 g hpre hpost

/-- **Scrub equality (resumption).** When a blocked caller resumes —
`blocked g` to `running` in one cycle — its register file is exactly its
saved file plus `rd := reply` for the single reply register recorded at
call time. -/
theorem caller_resumption (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (hreach : (machine m).Reachable σ)
    (d : DomainId) (g : GateId) (a : Activation)
    (hpre : (σ.doms d).run = .blocked g)
    (hact : (σ.gates g).act = some a)
    (hpost : ((step m σ).doms d).run = .running) :
    ∃ reply, ∀ r : RegId,
      ((step m σ).doms d).reg r =
        if r = a.callerRd ∧ r ≠ (0 : Fin numRegs) then reply
        else (σ.doms d).reg r := by
  have hwfσ : Wf σ := (Machines.Lnp64u.wfa_invariant m hwf σ hreach).1
  obtain ⟨a', reply, ha', _, hform⟩ := (step_touch m σ hwfσ d).2.1 g hpre hpost
  have haa : a' = a := by rw [hact] at ha'; exact (Option.some.inj ha').symm
  exact ⟨reply, fun r => by rw [hform r, haa]⟩

/-- **The frame.** A domain whose slice of the machine is untouched by
this cycle's four channels does not change: if `e` is not the executing
domain, not a party to a gate transition, not the target of a grant or a
revoke sweep, and not covered by Mover traffic, then `e`'s entire domain
state is equal before and after. (The channel enumeration is the
definition; the theorem says there is no fifth channel.) -/
theorem frame (m : Manifest) (hwf : m.WF)
    (σ : MachineState) (hreach : (machine m).Reachable σ) (e : DomainId)
    -- e is not executing and not in flight
    (hexec : ∀ fl, σ.inflight = some fl → fl.dom ≠ e)
    -- no gate transition involves e this cycle
    (hgate : ((step m σ).doms e).serving = (σ.doms e).serving ∧
             ((step m σ).doms e).run = (σ.doms e).run)
    -- e's capability table and lineage are untouched (no grant/transfer in,
    -- no revoke sweep across e)
    (hcaps : ((step m σ).doms e).caps = (σ.doms e).caps ∧
             ((step m σ).doms e).lineage = (σ.doms e).lineage) :
    ((step m σ).doms e).regs = (σ.doms e).regs ∧
    ((step m σ).doms e).pc = (σ.doms e).pc ∧
    ((step m σ).doms e).cause = (σ.doms e).cause := by
  have hwfσ : Wf σ := (Machines.Lnp64u.wfa_invariant m hwf σ hreach).1
  exact (step_touch m σ hwfσ e).2.2 hexec hgate.1 hgate.2

end Machines.Lnp64u.Theorems.T4
