import Machines.Lnp64u.Enc
import Machines.Lnp64u.Kernel

/-!
# System instruction set (11 ops), opcodes 16–26

Capability manipulation, memory mapping, gates, the Mover, and scheduling.
All state mechanics live in `Kernel.lean` as pure functions; these
declarations are thin monadic wrappers plus the errno/fault contracts.

## The packed descriptor word (`cap_dup`, `mem_grant`)

Narrowing and granting need more operands than three registers carry, and
the 4-word `move` descriptor must stay the ISA's only argblock — so these
two ops take a *packed descriptor* in `rs2`:

* `[1:0]`  target domain (`mem_grant` only; ignored by `cap_dup`)
* `[4:2]`  permissions r/w/x (must narrow, and satisfy W^X)
* `[16:5]` base offset in words, relative to the parent capability's base
* `[29:17]` length in words

## Handle-word conventions

A zero word is the null handle: `gate_call`/`gate_return` treat it as "no
capability transferred". Valid handles always have generation ≥ 1, so null
is unconstructible from live capabilities (T1).
-/

namespace Machines.Lnp64u.Isa

open Machines.Lnp64u Loom.Isa SpecM

/-! ## Descriptor and handle helpers -/

def descDom (w : Loom.Word32) : DomainId :=
  ⟨(w.extractLsb' 0 2).toNat, (w.extractLsb' 0 2).isLt⟩

def descPerms (w : Loom.Word32) : Perms :=
  { r := w.getLsbD 2, w := w.getLsbD 3, x := w.getLsbD 4 }

def descOff (w : Loom.Word32) : BitVec 12 := w.extractLsb' 5 12

def descLen (w : Loom.Word32) : BitVec 13 := w.extractLsb' 17 13

/-- Look up a live capability of `d` from a handle word, any class (the
handle's class bit must agree with the entry). Returns slot, generation,
entry. -/
def capLive (d : DomainId) (w : Loom.Word32) : SpecM (Slot × Gen × CapEntry) := do
  let h := Handle.decode w
  let σ ← get
  match (σ.doms d).liveCap h.slot h.gen with
  | none => raise .staleHandle
  | some e => do
      require (h.cls = e.kind.cls) .badCap
      pure (h.slot, h.gen, e)

/-- Allocate a derived capability in `owner`'s table (slot + lineage cell),
returning the `owner`-relative handle word. -/
def allocDerived (owner : DomainId) (kind : CapKind) (parent : CapRef) :
    SpecM Loom.Word32 := do
  let σ ← get
  match σ.freeSlot owner with
  | none => raise .slotOccupied
  | some s =>
      match σ.freeCell owner with
      | none => raise .noLineage
      | some l => do
          let (σ', ref) := σ.installDerived owner s l kind parent
          set σ'
          pure (Handle.encode ⟨s, ref.gen, kind.cls⟩)

/-- Check a narrow request against a parent memory capability; returns the
narrowed kind. -/
def narrow (base : Addr) (len : BitVec 13) (perms : Perms) (dw : Loom.Word32) :
    SpecM CapKind := do
  let off := descOff dw
  let nlen := descLen dw
  let np := descPerms dw
  require (decide (off.toNat + nlen.toNat ≤ len.toNat)) .outOfRange
  require (np.le perms) .permDenied
  require np.wx .permDenied
  pure (.mem (base + off) nlen np)

/-- Transfer the capability named by handle word `hw` (0 = none) from `d`
to `to_`, returning the `to_`-relative handle word (0 = none). Shared by
`gate_call` (argument) and `gate_return` (reply). -/
def transferByHandle (d : DomainId) (to_ : DomainId) (hw : Loom.Word32) :
    SpecM Loom.Word32 := do
  if hw = 0 then pure 0
  else do
    let (s, _, e) ← capLive d hw
    let σ ← get
    match σ.transferCap d s to_ with
    | none => raise .slotOccupied
    | some (σ', ref) => do
        set σ'
        pure (Handle.encode ⟨ref.slot, ref.gen, e.kind.cls⟩)

/-! ## The declarations -/

def system : List Instr := [
  { mnemonic := "cap_dup", opcode := 16, operands := ["rd", "rs1", "rs2"]
    sem :=
      { exec := fun c => do
          let hw ← reg c.d c.op.rs1
          let dw ← reg c.d c.op.rs2
          let (s, g, e) ← capLive c.d hw
          let kind ←
            match e.kind with
            | .mem base len perms => narrow base len perms dw
            | .gate gid => pure (.gate gid)
          let h ← allocDerived c.d kind ⟨c.d, s, g⟩
          setReg c.d c.op.rd h
        errs := [.staleHandle, .badCap, .outOfRange, .permDenied,
                 .slotOccupied, .noLineage] }
    cost := .capOp
    prose := { summary := "Duplicate (and narrow) a capability."
               operation := "A new capability derived from `rs1`'s is \
                 installed in the caller's lowest free slot; `rd` receives \
                 its handle. Memory capabilities are narrowed by the packed \
                 descriptor in `rs2` (subrange and non-escalating W^X \
                 permissions); gate capabilities copy as-is. Consumes one \
                 lineage cell of the caller." } },

  { mnemonic := "cap_drop", opcode := 17, operands := ["rd", "rs1"]
    sem :=
      { exec := fun c => do
          let hw ← reg c.d c.op.rs1
          let (s, g, _) ← capLive c.d hw
          let ref : CapRef := ⟨c.d, s, g⟩
          let σ ← get
          let σ' :=
            match σ.parentOf c.d s with
            | some p => σ.reparent ref p
            | none => σ.orphanChildren ref
          set (((σ'.clearSlot c.d s).sweepRegions).sweepMover)
          setReg c.d c.op.rd 0
        errs := [.staleHandle, .badCap] }
    cost := .capOp
    prose := { summary := "Drop a capability."
               operation := "The slot is freed and its generation retired \
                 (never reused). Children are spliced to the dropped \
                 capability's parent (or become roots if it had none); the \
                 lineage cell is restored to the caller's quota; region \
                 registers and the Mover are swept, so cached authority \
                 never outlives the capability." } },

  { mnemonic := "cap_revoke", opcode := 18, operands := ["rd", "rs1"]
    sem :=
      { exec := fun c => do
          let hw ← reg c.d c.op.rs1
          let (s, g, e) ← capLive c.d hw
          require (e.kind.cls = .mem) .badCap
          let σ ← get
          let m := σ.marks ⟨c.d, s, g⟩
          set (((σ.destroyMarked m).sweepRegions).sweepMover)
          setReg c.d c.op.rd 0
        errs := [.staleHandle, .badCap] }
    cost := .revoke
    prose := { summary := "Revoke all descendants of a memory capability."
               operation := "Every capability derived (transitively) from \
                 `rs1`'s is destroyed machine-wide: entries cleared, slot \
                 generations retired, lineage cells restored. All region \
                 registers caching destroyed authority are swept, and a \
                 Mover transfer running under destroyed authority is \
                 aborted with `-ESTALE` in its status word. The revoked \
                 capability itself remains. When this instruction retires, \
                 no agent can access under any descendant (T3)." } },

  { mnemonic := "mem_grant", opcode := 19, operands := ["rd", "rs1", "rs2"]
    sem :=
      { exec := fun c => do
          let hw ← reg c.d c.op.rs1
          let dw ← reg c.d c.op.rs2
          let (s, g, e) ← capLive c.d hw
          match e.kind with
          | .gate _ => raise .badCap
          | .mem base len perms => do
              let kind ← narrow base len perms dw
              let h ← allocDerived (descDom dw) kind ⟨c.d, s, g⟩
              setReg c.d c.op.rd h
        errs := [.staleHandle, .badCap, .outOfRange, .permDenied,
                 .slotOccupied, .noLineage] }
    cost := .capOp
    prose := { summary := "Grant a memory subrange to another domain."
               operation := "A capability narrowed from `rs1`'s by the \
                 packed descriptor in `rs2` is installed in the target \
                 domain's lowest free slot, consuming one of the target's \
                 lineage cells. `rd` receives the *target-relative* handle \
                 word, which the granter must convey to the target through \
                 an existing channel (granted memory or a gate)." } },

  { mnemonic := "map", opcode := 20, operands := ["rd", "rs1", "imm"]
    sem :=
      { exec := fun c => do
          let hw ← reg c.d c.op.rs1
          let (s, g, e) ← capLive c.d hw
          match e.kind with
          | .gate _ => raise .badCap
          | .mem base len perms => do
              let ri : RegionId :=
                ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
              let rgn : Region := { base := base, len := len, perms := perms
                                    backing := ⟨c.d, s, g⟩ }
              updDom c.d fun ds =>
                { ds with regions := Loom.Fun.update ds.regions ri (some rgn) }
              setReg c.d c.op.rd 0
        errs := [.staleHandle, .badCap] }
    cost := .capOp
    prose := { summary := "Map a memory capability into a region register."
               operation := "Region register `imm[1:0]` caches `rs1`'s \
                 authority (base, length, permissions, and the backing \
                 reference). Loads, stores, and fetches check region \
                 registers only; the sweep in `cap_drop`/`cap_revoke` \
                 clears regions whose backing dies." } },

  { mnemonic := "unmap", opcode := 21, operands := ["rd", "imm"]
    sem :=
      { exec := fun c => do
          let ri : RegionId :=
            ⟨(c.op.imm.extractLsb' 0 2).toNat, (c.op.imm.extractLsb' 0 2).isLt⟩
          updDom c.d fun ds =>
            { ds with regions := Loom.Fun.update ds.regions ri none }
          setReg c.d c.op.rd 0 }
    cost := .capOp
    prose := { summary := "Clear a region register."
               operation := "Region register `imm[1:0]` is cleared; \
                 subsequent accesses relying on it fault." } },

  { mnemonic := "gate_call", opcode := 22, operands := ["rd", "rs1", "rs2"]
    sem :=
      { exec := fun c => do
          let hw ← reg c.d c.op.rs1
          let (_, _, e) ← capLive c.d hw
          match e.kind with
          | .mem .. => raise .badCap
          | .gate gid => do
              let σ ← get
              let gs := σ.gates gid
              require gs.act.isNone .gateBusy
              let cal := gs.config.callee
              require (decide (cal ≠ c.d)) .gateBusy
              require (decide ((σ.doms cal).run = .running)) .gateBusy
              require (σ.doms cal).serving.isNone .gateBusy
              let depth :=
                match (σ.doms c.d).serving with
                | some g' =>
                    match (σ.gates g').act with
                    | some a => a.depth + 1
                    | none => 1
                | none => 1
              require (decide (depth ≤ maxChainDepth)) .gateBusy
              let argw ← reg c.d c.op.rs2
              let argHandle ← transferByHandle c.d cal argw
              let σ ← get
              let cd := σ.doms cal
              let act : Activation :=
                { caller := c.d, callerRd := c.op.rd
                  savedRegs := cd.regs, savedPc := cd.pc
                  savedServing := cd.serving, depth := depth }
              set ({ σ with
                gates := Loom.Fun.update σ.gates gid { gs with act := some act } })
              updDom cal fun ds =>
                { ds with
                  regs := fun r => if r = (1 : Fin numRegs) then argHandle else 0
                  pc := gs.config.entry
                  serving := some gid }
              updDom c.d fun ds => { ds with run := .blocked gid }
        errs := [.staleHandle, .badCap, .gateBusy, .slotOccupied, .noLineage] }
    cost := .gate
    prose := { summary := "Call through a gate (the one blocking construct)."
               operation := "The caller suspends; the gate's callee domain \
                 is activated at the gate's entry point with a scrubbed \
                 register file — `r1` holds the transferred capability's \
                 callee-relative handle (or 0), every other register is \
                 zero. At most one capability transfers per call (`rs2`, 0 \
                 = none); the gate is serialized; chain depth is bounded by \
                 4; a domain never serves two activations at once."
               notes := ["Errno is returned to the *caller* without \
                 suspension when the gate is busy, the chain is full, or \
                 the transfer cannot be placed."] } },

  { mnemonic := "gate_return", opcode := 23, operands := ["rd", "rs1"]
    sem :=
      { exec := fun c => do
          let σ ← get
          match (σ.doms c.d).serving with
          | none => fatal .protocol
          | some gid =>
              match (σ.gates gid).act with
              | none => fatal .protocol
              | some act => do
                  let rw ← reg c.d c.op.rs1
                  let reply ← transferByHandle c.d act.caller rw
                  let σ ← get
                  set ({ σ with
                    gates := Loom.Fun.update σ.gates gid
                      { (σ.gates gid) with act := none } })
                  updDom c.d fun ds =>
                    { ds with regs := act.savedRegs, pc := act.savedPc
                              serving := act.savedServing }
                  updDom act.caller fun ds => { ds with run := .running }
                  setReg act.caller act.callerRd reply
        errs := [.staleHandle, .badCap, .slotOccupied, .noLineage]
        faults := [.protocol] }
    cost := .gate
    prose := { summary := "Return from a gate activation."
               operation := "The serving domain's saved context is \
                 restored; the suspended caller resumes with exactly its \
                 saved register file plus `rd := reply` — the reply is the \
                 caller-relative handle of the transferred capability \
                 (`rs1`, 0 = none). Executing `gate_return` outside an \
                 activation is a protocol fault (domain-fatal)." } },

  { mnemonic := "move", opcode := 24, operands := ["rd", "rs1"]
    sem :=
      { exec := fun c => do
          let σ0 ← get
          require σ0.mover.isNone .moverBusy
          let aw ← reg c.d c.op.rs1
          let base : Addr := aw.setWidth 12
          let srcH ← load c.d base
          let dstH ← load c.d (base + 1)
          let lenW ← load c.d (base + 2)
          let stW ← load c.d (base + 3)
          let (ss, gs_, es) ← capLive c.d srcH
          let (sd, gd, ed) ← capLive c.d dstH
          match es.kind, ed.kind with
          | .mem sb sl sp, .mem db dl dp => do
              require sp.r .permDenied
              require dp.w .permDenied
              let n := lenW.toNat
              require (decide (n ≤ sl.toNat) && decide (n ≤ dl.toNat)) .outOfRange
              let sa : Addr := stW.setWidth 12
              let σ ← get
              demand (σ.domCovers c.d sa { r := false, w := true, x := false })
                .memoryAuthority
              let job : MoverJob :=
                { owner := c.d, src := ⟨c.d, ss, gs_⟩, dst := ⟨c.d, sd, gd⟩
                  srcCur := sb, dstCur := db, remaining := n
                  statusAddr := sa }
              set ({ σ with mover := some job })
              setReg c.d c.op.rd 0
          | _, _ => raise .badCap
        errs := [.staleHandle, .badCap, .permDenied, .outOfRange, .moverBusy]
        faults := [.memoryAuthority] }
    cost := .mover
    prose := { summary := "Program the Mover."
               operation := "`rs1` points at the ISA's only argblock, the \
                 4-word move descriptor: source handle, destination handle, \
                 word count, status-word address. Both capabilities must be \
                 the caller's, readable/writable respectively, and cover \
                 the count. The Mover then copies one word per cycle, \
                 re-checking both capabilities' generations, ranges, and \
                 permissions every word; on completion it writes 1 to the \
                 caller-owned status word, on a failed re-check it writes \
                 `-ESTALE` and stops." } },

  { mnemonic := "yield", opcode := 25, operands := ["rd"]
    sem :=
      { exec := fun c => do
          updDom c.d fun ds => { ds with budget := 0 }
          setReg c.d c.op.rd 0 }
    cost := .sched
    prose := { summary := "Yield the rest of this period's budget."
               operation := "The caller's remaining budget for the current \
                 period becomes zero; it is rescheduled at its next period \
                 refill." } },

  { mnemonic := "halt", opcode := 26, operands := []
    sem :=
      { exec := fun c => do
          updDom c.d fun ds => { ds with run := .halted } }
    cost := .sched
    prose := { summary := "Halt this domain."
               operation := "The domain halts voluntarily; its cause \
                 register stays 0 (distinguishing `halt` from a fault). \
                 Halting is terminal — µ has no domain restart." } }
]

end Machines.Lnp64u.Isa
