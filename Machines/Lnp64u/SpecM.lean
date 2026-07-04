-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Manifest

/-!
# The semantics monad (L0)

Instruction semantics are written in `SpecM`: a state transformer over
`MachineState` with three-way outcomes matching the T6 outcome set —

* `ok`    — the instruction retires normally;
* `err e` — the instruction retires with `-errno` in `rd` (the recoverable
  path; the retire glue writes the register, so the per-op return ABI is
  uniform by construction — half of T1's ABI bound);
* `fault f` — domain-fatal: **no architectural effect** from the faulting
  instruction (the `Res.fault` constructor carries no state), the domain
  halts with the cause register set by the retire glue in `Step.lean`.

Total by construction: no partiality anywhere; every instruction's `exec`
is a Lean function.

Convention (enforced by review, cheap at µ scale): `errno`/`fault` are
raised before any mutation, so `err` outcomes also have no architectural
effect beyond the `rd` write.
-/

namespace Machines.Lnp64u

/-- Outcome of running a semantics fragment. -/
inductive Res (α : Type) where
  | ok (a : α) (σ : MachineState)
  | err (e : Errno) (σ : MachineState)
  | fault (f : Fault)

/-- The semantics monad. -/
def SpecM (α : Type) : Type := MachineState → Res α

namespace SpecM

instance : Monad SpecM where
  pure a := fun σ => .ok a σ
  bind x f := fun σ =>
    match x σ with
    | .ok a σ' => f a σ'
    | .err e σ' => .err e σ'
    | .fault f' => .fault f'

/-- Read the whole machine state. -/
def get : SpecM MachineState := fun σ => .ok σ σ

/-- Replace the whole machine state. -/
def set (σ' : MachineState) : SpecM Unit := fun _ => .ok () σ'

/-- Update the machine state. -/
def modify (f : MachineState → MachineState) : SpecM Unit :=
  fun σ => .ok () (f σ)

/-- Retire with `-errno` (recoverable failure). -/
def raise {α : Type} (e : Errno) : SpecM α := fun σ => .err e σ

/-- Domain-fatal fault: discards all effects of this instruction. -/
def fatal {α : Type} (f : Fault) : SpecM α := fun _ => .fault f

/-- Raise `e` unless `cond` holds. -/
def require (cond : Bool) (e : Errno) : SpecM Unit :=
  if cond then pure () else raise e

/-- Fault with `f` unless `cond` holds. -/
def demand (cond : Bool) (f : Fault) : SpecM Unit :=
  if cond then pure () else fatal f

/-! ## Domain-relative accessors -/

/-- Read register `r` of domain `d` (architectural: `r0` reads 0). -/
def reg (d : DomainId) (r : RegId) : SpecM Loom.Word32 :=
  fun σ => .ok ((σ.doms d).reg r) σ

/-- Write register `r` of domain `d` (writes to `r0` discarded). -/
def setReg (d : DomainId) (r : RegId) (v : Loom.Word32) : SpecM Unit :=
  modify (·.setDom d (·.setReg r v))

/-- Update domain `d`. -/
def updDom (d : DomainId) (f : DomainState → DomainState) : SpecM Unit :=
  modify (·.setDom d f)

/-- Load a word as domain `d`: region-register authority or fault (the only
path from a domain to memory). -/
def load (d : DomainId) (a : Addr) : SpecM Loom.Word32 := do
  let σ ← get
  demand (σ.domCovers d a { r := true, w := false, x := false }) .memoryAuthority
  pure (σ.read a)

/-- Store a word as domain `d`, under region-register authority. -/
def store (d : DomainId) (a : Addr) (v : Loom.Word32) : SpecM Unit := do
  let σ ← get
  demand (σ.domCovers d a { r := false, w := true, x := false }) .memoryAuthority
  set (σ.write a v)

/-- Look up a *live* capability of domain `d` from a register handle word:
decodes the handle, checks slot generation and class. The single entry path
from register values to authority. -/
def capFromHandle (d : DomainId) (w : Loom.Word32) (cls : CapClass) :
    SpecM (Slot × CapEntry) := do
  let h := Handle.decode w
  let σ ← get
  match (σ.doms d).liveCap h.slot h.gen with
  | none => raise .staleHandle
  | some e => do
      require (e.kind.cls = cls && h.cls = cls) .badCap
      pure (h.slot, e)

end SpecM

/-- Decoded operand fields, per D1's layout: `opcode [5:0]`, `rd [8:6]`,
`rs1 [11:9]`, `rs2 [14:12]`, `imm17 [31:15]`. -/
structure Operands where
  rd  : RegId
  rs1 : RegId
  rs2 : RegId
  imm : BitVec 17
deriving Repr, DecidableEq

/-- Execution context of one instruction: the executing domain and the
address the instruction was fetched from (branch targets are computed from
it; the retire glue has already advanced `pc` when `exec` runs). -/
structure Ctx where
  d  : DomainId
  pc : Addr
  op : Operands

/-- The LNP64-µ semantics payload for `Loom.Isa.InstrDecl`. -/
abbrev Exec := Ctx → SpecM Unit

end Machines.Lnp64u
