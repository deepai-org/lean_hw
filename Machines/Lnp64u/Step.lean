-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Isa
import Loom.Core.Ts

/-!
# The machine step: one cycle (L0, P7)

`step m : MachineState → MachineState` is one cycle of the configured
machine, fully deterministic. Phases, in order:

1. **Refill** — every domain whose period boundary is this cycle gets its
   budget back.
2. **Core** — if an instruction is in flight, burn one cycle; on its last
   cycle it *retires atomically*: `pc` advances, then `exec` runs against
   the current state (the snapshot rule — retirement is the linearization
   point). If the core is idle, the scheduler issues: the highest-priority
   running domain whose *payer* (donation: the origin of its serving chain)
   has any budget attempts fetch → decode → upfront budget charge; fetch or
   decode failure is a domain-fatal fault consuming the cycle; insufficient
   payer budget is chargeable too: a non-serving domain burns its residual
   payer budget to zero, while a serving domain raises a budget fault so
   the serving chain unwinds instead of replaying an unchargeable stall.
3. **Mover** — one word: both capabilities are re-looked-up (generation,
   range, permission) in the *current* tables; a failed re-check aborts the
   job and reports `-ESTALE` through the status word (itself written only
   under the owner's still-current authority); the final word writes 1.
4. The cycle counter advances.

Budget is charged upfront at issue (simplifies T9's accounting; T7 quotes
`WcetClass.cost` either way). A mid-flight refill may top the payer back up;
the in-flight instruction is already paid for.
-/

namespace Machines.Lnp64u

open Loom

/-- Phase 1: period-boundary budget refill.

The boundary test reads the **wrapping** 32-bit counter; with
`Manifest.WF.period_dvd` (`periodP ∣ 2 ^ 32`) the boundaries stay exactly
`periodP` apart across the wrap. There is deliberately no "skip at boot"
guard: with a wrapping counter, `cycle = 0` at boot is indistinguishable
from `cycle = 0` after a wrap, and the wrap boundary *must* refill (else a
domain would wait up to `2·periodP` there). At boot the refill is a no-op —
`initState` already carries the full quota `Q`. The hardware
(`Hw.refillCondE`) tests the same condition via the hidden mod-`P`
counters. -/
def refillPhase (m : Manifest) (σ : MachineState) : MachineState :=
  { σ with doms := fun d =>
      let ds := σ.doms d
      let cfg := m.doms d
      if σ.cycle.toNat % cfg.periodP = 0 then { ds with budget := cfg.budgetQ } else ds }

/-- Fetch the instruction word at `d`'s PC, requiring execute authority via
a region register. -/
def fetch (σ : MachineState) (d : DomainId) : Option Loom.Word32 :=
  if σ.domCovers d (σ.doms d).pc { r := false, w := false, x := true }
  then some (σ.read (σ.doms d).pc)
  else none

/-- Halt domain `d` with fault `f` (cause register set), unwinding any
gate activation `d` was serving (T6). -/
def haltWith (σ : MachineState) (d : DomainId) (f : Fault) : MachineState :=
  σ.haltDom d (BitVec.ofNat 32 f.code)

/-- The scheduler: highest-priority domain that is running and whose payer
has budget remaining. Distinct priorities (manifest WF) make the choice
unique. -/
def schedule (m : Manifest) (σ : MachineState) : Option DomainId :=
  ((List.finRange numDomains).filter fun d =>
      decide ((σ.doms d).run = .running) && decide (0 < (σ.doms (σ.payer d)).budget))
    |>.foldl (init := none) fun best d =>
      match best with
      | none => some d
      | some b => if (m.doms b).priority < (m.doms d).priority then some d else some b

/-- Retire the in-flight instruction: advance `pc`, run `exec` on the
current state, apply the outcome (T6's outcome set: retire / `-errno` /
domain-fatal). Decode is re-run on the latched word; it succeeded at issue
and the word is latched, so the `none` arm is unreachable (kept total). -/
def retire (σ : MachineState) (d : DomainId) (w : Loom.Word32) : MachineState :=
  match Loom.Isa.decode isa w with
  | none => haltWith σ d .illegalInstruction
  | some instr =>
      let thisPc := (σ.doms d).pc
      let op := operandsOf w
      let σ₁ := σ.setDom d fun ds => { ds with pc := ds.pc + 1 }
      match instr.sem.exec { d := d, pc := thisPc, op := op } σ₁ with
      | .ok _ σ' => σ'
      | .err e σ' => σ'.setDom d fun ds => ds.setReg op.rd e.toWord
      | .fault f => haltWith σ d f

/-- Phase 2: the core. -/
def corePhase (m : Manifest) (σ : MachineState) : MachineState :=
  match σ.inflight with
  | some fl =>
      if fl.cyclesLeft ≤ 1 then
        retire { σ with inflight := none } fl.dom fl.word
      else
        { σ with inflight := some { fl with cyclesLeft := fl.cyclesLeft - 1 } }
  | none =>
      match schedule m σ with
      | none => σ
      | some d =>
          match fetch σ d with
          | none => haltWith σ d .memoryAuthority
          | some w =>
              match Loom.Isa.decode isa w with
              | none => haltWith σ d .illegalInstruction
              | some instr =>
                  let cost := instr.cost.cost
                  let p := σ.payer d
                  if cost ≤ (σ.doms p).budget then
                    -- donation check: a serving domain draws its activation down
                    match (σ.doms d).serving with
                    | some g =>
                        match (σ.gates g).act with
                        | some a =>
                            if cost ≤ a.donated then
                              let σ' := σ.setDom p fun ds =>
                                { ds with budget := ds.budget - cost }
                              let gs' : GateState :=
                                { (σ'.gates g) with
                                  act := some { a with donated := a.donated - cost } }
                              let σ'' := { σ' with gates := Loom.Fun.update σ'.gates g gs' }
                              { σ'' with inflight := some { dom := d, word := w, cyclesLeft := cost } }
                            else
                              -- donation exhausted: forced unwind (T6)
                              haltWith σ d .budget
                        | none => haltWith σ d .protocol
                    | none =>
                        let σ' := σ.setDom p fun ds => { ds with budget := ds.budget - cost }
                        { σ' with inflight := some { dom := d, word := w, cyclesLeft := cost } }
                  else
                    match (σ.doms d).serving with
                    | some _ => haltWith σ d .budget
                    | none => σ.setDom p fun ds => { ds with budget := 0 }

/-- Does the live capability behind `r` currently cover `a` with `need`?
The Mover's per-word re-check: generation, range, and permission against
the *current* table. -/
def moverCheck (σ : MachineState) (r : CapRef) (a : Addr) (need : Perms) : Bool :=
  match (σ.doms r.dom).liveCap r.slot r.gen with
  | some e => e.kind.covers a need
  | none => false

/-- Write the Mover status word under the owner's current authority; a
failed authority check drops the write (the owner unmapped or lost its
status range — there is no one left to tell). -/
def moverStatus (σ : MachineState) (job : MoverJob) (v : Loom.Word32) : MachineState :=
  if σ.domCovers job.owner job.statusAddr { r := false, w := true, x := false }
  then σ.write job.statusAddr v
  else σ

/-- Phase 3: the Mover moves one word (or aborts, or completes). -/
def moverPhase (σ : MachineState) : MachineState :=
  match σ.mover with
  | none => σ
  | some job =>
      if job.remaining = 0 then
        moverStatus { σ with mover := none } job 1
      else if moverCheck σ job.src job.srcCur { r := true, w := false, x := false } &&
              moverCheck σ job.dst job.dstCur { r := false, w := true, x := false } then
        let σ' := σ.write job.dstCur (σ.read job.srcCur)
        let job' : MoverJob :=
          { job with srcCur := job.srcCur + 1, dstCur := job.dstCur + 1
                     remaining := job.remaining - 1 }
        if job'.remaining = 0 then
          moverStatus { σ' with mover := none } job' 1
        else
          { σ' with mover := some job' }
      else
        moverStatus { σ with mover := none } job Errno.staleHandle.toWord

/-- One cycle. -/
def step (m : Manifest) (σ : MachineState) : MachineState :=
  let σ₁ := refillPhase m σ
  let σ₂ := corePhase m σ₁
  let σ₃ := moverPhase σ₂
  { σ₃ with cycle := σ₃.cycle + 1 }

/-- `n` cycles. -/
def stepN (m : Manifest) : Nat → MachineState → MachineState
  | 0, σ => σ
  | n + 1, σ => stepN m n (step m σ)

/-- The configured machine as a transition system (P2): the abstract side
of the multicycle refinement (R-MC) and the subject of T2–T9. -/
def machine (m : Manifest) : Loom.TSys :=
  Loom.TSys.ofFun MachineState (fun σ => σ = m.initState) (step m)

end Machines.Lnp64u
