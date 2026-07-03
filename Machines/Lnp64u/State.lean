import Loom.Core.Fun
import Machines.Lnp64u.Cap

/-!
# Machine state (L0)

The complete architectural state of LNP64-µ. Design decisions recorded here:

* **The spec is cycle-accurate.** One `Step.step` (see `Step.lean`) is one
  cycle. An instruction occupies the core for its WCET-class cost and its
  effect applies *atomically at retirement* — the snapshot rule: engine
  snapshot points map onto atomic rules (L3), and the retirement is the
  linearization point. The in-flight instruction is the fetched raw word
  (fetch snapshots the instruction memory at issue; data reads happen at
  retirement).

* **One core, one Mover.** "A domain running its own thread" is virtual —
  domains share the core via the scheduler, so a gate activation always
  preempts its callee at an instruction boundary.

* **Gate activations do not stack.** A domain serves at most one activation
  (`serving`); µ has no continuation stack (that is a later rung of the
  ladder). The chain-depth bound and the holder/deadlock check both fall out
  of this plus the activation records.

* Prop-level state uses functions for memory and tables (decision D5); the
  packed bit-level face lives in `BitLevel.lean` with a proved
  correspondence.
-/

namespace Machines.Lnp64u

/-- Scheduling status of a domain. A domain *serving* a gate activation is
`running`; the suspended caller is `blocked`. Faults and `halt` are both
terminal (`halted`); the cause register distinguishes them. -/
inductive RunState where
  /-- Eligible for scheduling (possibly serving a gate activation). -/
  | running
  /-- Suspended in `gate_call`, awaiting the matching `gate_return`. -/
  | blocked (g : GateId)
  /-- Terminal: voluntary `halt` (cause 0) or domain-fatal fault. -/
  | halted
deriving Repr, DecidableEq

/-- Per-domain architectural state. -/
structure DomainState where
  /-- The register file. `r0` is hardwired: reads of register 0 yield 0
  regardless of this function's value at 0 (see `DomainState.reg`). -/
  regs : RegId → Loom.Word32
  /-- The program counter, a word address. -/
  pc : Addr
  /-- The capability table. -/
  caps : Slot → Option CapEntry
  /-- Current generation of each slot. Stamped on the occupying entry;
  bumped (saturating at `genRetired`) whenever the slot is freed. -/
  slotGen : Slot → Gen
  /-- The lineage table. Occupied cells are the T9 lineage resource. -/
  lineage : LineageId → Option LineageCell
  /-- Region registers: cached memory authority, swept by revoke. -/
  regions : RegionId → Option Region
  /-- Scheduling status. -/
  run : RunState
  /-- If `some g`, this domain is currently executing gate `g`'s activation. -/
  serving : Option GateId
  /-- The cause register: 0 while no fault has occurred. -/
  cause : Loom.Word32
  /-- Budget remaining in the current period, in cycles. -/
  budget : Nat
  /-- Static copy of this domain's manifest donation bound: the cycle
  budget each gate activation *called by this domain* may consume before
  it is forcibly unwound (T6). -/
  maxDonation : Nat

namespace DomainState

/-- Architectural register read: `r0` reads as zero. -/
def reg (d : DomainState) (r : RegId) : Loom.Word32 :=
  if r = (0 : Fin numRegs) then 0 else d.regs r

/-- Architectural register write: writes to `r0` are discarded. -/
def setReg (d : DomainState) (r : RegId) (v : Loom.Word32) : DomainState :=
  if r = (0 : Fin numRegs) then d else { d with regs := Loom.Fun.update d.regs r v }

/-- Look up a live capability: entry present *and* handle generation matches
the slot's current generation. The single validity test every consumer
(instructions, Mover re-check, region sweep) goes through. -/
def liveCap (d : DomainState) (s : Slot) (g : Gen) : Option CapEntry :=
  match d.caps s with
  | some e => if d.slotGen s = g && g != 0 then some e else none
  | none => none

end DomainState

/-- Static configuration of one gate: which domain serves it, and where its
activation enters. Copied from the manifest at boot (gates are static). -/
structure GateConfig where
  callee : DomainId
  entry  : Addr
deriving Repr, DecidableEq

/-- A gate activation record: created by `gate_call`, consumed by
`gate_return`. Saves the *callee's* preempted context; the blocked caller's
registers stay in place in its own `DomainState`. -/
structure Activation where
  /-- The suspended caller. -/
  caller : DomainId
  /-- Caller's destination register for the reply (T4: caller resumption =
  saved file plus `rd := reply`). -/
  callerRd : RegId
  /-- Callee context saved at activation entry. -/
  savedRegs : RegId → Loom.Word32
  savedPc : Addr
  /-- What the callee was serving before this activation preempted it —
  `none` always in µ (activations do not stack); kept as the field full
  LNP64's continuation stack generalizes (Rule 3). -/
  savedServing : Option GateId
  /-- Chain depth of this activation (1 = called from a non-serving domain).
  Bounded by `maxChainDepth`. -/
  depth : Nat
  /-- Donation cycles remaining: decremented at every issue by the serving
  domain; exhaustion is a `budget` fault, which unwinds the activation
  (T6's no-hostage bound is `f(maxDonation, depth, Mover word + sweep)`). -/
  donated : Nat

/-- Per-gate dynamic state: the serialized construct is one optional
activation. The holder field *is* `Activation` existence plus the callee's
`serving` mark. -/
structure GateState where
  config : GateConfig
  act : Option Activation

/-- The Mover's programmed transfer. Source and destination are re-validated
against the *current* cap tables every word (generation, range, permission)
— the mechanism T3 leans on for in-flight revocation. -/
structure MoverJob where
  /-- The domain that issued `move` (owner of the status word). -/
  owner : DomainId
  /-- Source capability, by frozen reference; re-checked per word. -/
  src : CapRef
  /-- Destination capability, by frozen reference; re-checked per word. -/
  dst : CapRef
  /-- Next source / destination word addresses. -/
  srcCur : Addr
  dstCur : Addr
  /-- Words remaining. -/
  remaining : Nat
  /-- Caller-owned status word address (validated writable at `move` time,
  re-checked at completion/abort write). -/
  statusAddr : Addr

/-- The in-flight instruction: raw fetched word, owning domain, and cycles
until retirement. -/
structure InFlight where
  dom : DomainId
  word : Loom.Word32
  cyclesLeft : Nat

/-- The complete machine state. -/
structure MachineState where
  /-- Global cycle counter (drives period refill). -/
  cycle : Nat
  /-- Physical memory, one word per address (D5: function at Prop level). -/
  mem : Addr → Loom.Word32
  doms : DomainId → DomainState
  gates : GateId → GateState
  mover : Option MoverJob
  inflight : Option InFlight

namespace MachineState

/-- Read memory. -/
def read (σ : MachineState) (a : Addr) : Loom.Word32 := σ.mem a

/-- Write memory. -/
def write (σ : MachineState) (a : Addr) (v : Loom.Word32) : MachineState :=
  { σ with mem := Loom.Fun.update σ.mem a v }

/-- Update one domain. -/
def setDom (σ : MachineState) (d : DomainId) (f : DomainState → DomainState) :
    MachineState :=
  { σ with doms := Loom.Fun.update σ.doms d (f (σ.doms d)) }

/-- Does domain `d` have memory authority for `a` with `need`, via any
region register? This is the *only* path from a domain to memory. -/
def domCovers (σ : MachineState) (d : DomainId) (a : Addr) (need : Perms) : Bool :=
  decide (∃ r : RegionId, ∃ rg, (σ.doms d).regions r = some rg ∧ rg.covers a need)

/-- Walk to the origin of a serving chain: the domain whose budget pays for
`d`'s execution (donation semantics). Fuel-bounded by `maxChainDepth`. -/
def chainOrigin (σ : MachineState) : Nat → DomainId → DomainId
  | 0, d => d
  | fuel + 1, d =>
      match (σ.doms d).serving with
      | none => d
      | some g =>
          match (σ.gates g).act with
          | some a => σ.chainOrigin fuel a.caller
          | none => d

/-- The budget payer for domain `d`. -/
def payer (σ : MachineState) (d : DomainId) : DomainId :=
  σ.chainOrigin maxChainDepth d

end MachineState
end Machines.Lnp64u
