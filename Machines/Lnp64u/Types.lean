import Loom.Core.Word

/-!
# Machine-wide scalar types and frozen parameters (L0)

The µ instantiation constants and the small enumerated types every other Spec
file builds on. Everything here is a decision recorded once: widths, counts,
the errno table, fault causes, and WCET classes. Changing a number here is a
change to the machine.

Decision D1 (encoding layout) is recorded in `EncodingLayout` field positions
in `Instr.lean`; the widths it depends on (opcode 6 bits, reg fields 3 bits)
are fixed here.
-/

namespace Machines.Lnp64u

/-! ## Frozen µ parameters -/

/-- Number of static domains. -/
abbrev numDomains : Nat := 4
/-- General-purpose registers per domain (`r0` reads as zero). -/
abbrev numRegs : Nat := 8
/-- Capability slots per domain. -/
abbrev numSlots : Nat := 16
/-- Region registers per domain (cached memory authority, swept by revoke). -/
abbrev numRegions : Nat := 4
/-- Lineage cells per domain (the per-domain lineage quota — a global pool
would be a cross-domain exhaustion channel violating T5/T9 jointly). -/
abbrev numLineage : Nat := 16
/-- Maximum gate-call chain depth. -/
abbrev maxChainDepth : Nat := 4
/-- Number of gates in the machine (manifest-configured). -/
abbrev numGates : Nat := 4
/-- Physical memory size in 32-bit words (16 KiB). -/
abbrev memWords : Nat := 4096

/-! ## Identifier types -/

/-- A static domain identifier. -/
abbrev DomainId := Fin numDomains
/-- A general-purpose register name; `r0` is hardwired to zero. -/
abbrev RegId := Fin numRegs
/-- A capability-slot index within one domain's cap table. -/
abbrev Slot := Fin numSlots
/-- A region-register index. -/
abbrev RegionId := Fin numRegions
/-- A lineage-cell index within one domain's lineage table. -/
abbrev LineageId := Fin numLineage
/-- A gate identifier. -/
abbrev GateId := Fin numGates

/-- A capability generation. Generation `0` is the null generation: no valid
capability ever carries it (T1's null-handle unconstructibility), and
retirement advances a slot's generation so stale handles die. -/
abbrev Gen := Loom.Word8

/-- A word-aligned physical address, i.e. a word index into physical memory.
Byte addressing does not exist in µ: loads and stores are aligned word-only,
so the spec addresses words directly. -/
abbrev Addr := BitVec 12

/-! ## Error and fault vocabulary -/

/-- The `-errno` convention: system ops that fail *recoverably* return a
negative errno in `rd` and retire. Encoded as a word `(-e.code : Word32)`. -/
inductive Errno where
  /-- Handle's generation does not match the slot's current generation. -/
  | staleHandle
  /-- Named slot is empty or of the wrong capability class. -/
  | badCap
  /-- Requested range not contained in the source capability. -/
  | outOfRange
  /-- Destination slot already occupied. -/
  | slotOccupied
  /-- The domain's lineage quota is exhausted. -/
  | noLineage
  /-- Gate is busy (serialized construct) or chain depth would exceed 4. -/
  | gateBusy
  /-- Requested permissions exceed those held. -/
  | permDenied
  /-- The Mover is already executing a transfer for this domain. -/
  | moverBusy
  /-- The gate callee faulted, halted, or exhausted its donation while
  serving; the caller resumes with this errno (T6's no-hostage unwind). -/
  | calleeFault
deriving Repr, DecidableEq

/-- Numeric errno codes (stable ABI; the book quotes these). -/
def Errno.code : Errno → Nat
  | .staleHandle  => 1
  | .badCap       => 2
  | .outOfRange   => 3
  | .slotOccupied => 4
  | .noLineage    => 5
  | .gateBusy     => 6
  | .permDenied   => 7
  | .moverBusy    => 8
  | .calleeFault  => 9

/-- The `-errno` return word. -/
def Errno.toWord (e : Errno) : Loom.Word32 := -(BitVec.ofNat 32 e.code)

/-- Fault causes. Every fault is domain-fatal: the domain halts and the cause
lands in its cause register. There are no upcalls in µ. -/
inductive Fault where
  /-- Instruction word failed to decode. -/
  | illegalInstruction
  /-- Load or store outside all region registers, or without permission. -/
  | memoryAuthority
  /-- `gate_return` with no active call to return to. -/
  | protocol
  /-- Donation exhausted while serving a gate activation (the T6
  no-hostage enforcement: the activation unwinds, the caller resumes with
  `-ECALLEEFAULT`). -/
  | budget
deriving Repr, DecidableEq

/-- Numeric cause-register codes. Zero means "no fault"; the cause register
of a running domain reads zero. -/
def Fault.code : Fault → Nat
  | .illegalInstruction => 1
  | .memoryAuthority    => 2
  | .protocol           => 3
  | .budget             => 4

/-! ## WCET classes -/

/-- Worst-case-execution-time classes. Every instruction declares one; the
25 T7 WCET lemmas are stated per class ×  op, conditional on the clock
constraint. Bounds are in core cycles of the multicycle machine. -/
inductive WcetClass where
  /-- Pure register/ALU work: fixed small cycle count. -/
  | alu
  /-- One memory access plus region check. -/
  | mem
  /-- Capability-table manipulation, no sweep. -/
  | capOp
  /-- Revoke: bounded by the machine-wide sweep (regions + Mover ack). -/
  | revoke
  /-- Gate transfer: register scrub plus context switch. -/
  | gate
  /-- Mover programming (`move`): descriptor read plus handoff. -/
  | mover
  /-- Scheduling ops (`yield`, `halt`). -/
  | sched
deriving Repr, DecidableEq

end Machines.Lnp64u
