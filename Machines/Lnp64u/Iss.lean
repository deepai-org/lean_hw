import Machines.Lnp64u.Step
import Loom.Core.Trace

/-!
# LNP64-µ instruction-set simulator

The spec is the simulator (P7): `run` iterates `step`. Trace events are
*derived* alongside the same pure phase functions `step` composes — the
event extractor is untrusted tooling (lockstep corroboration), the state
evolution is the one `step` the theorems are about.

`demoManifest` is the checked-in golden configuration: four domains,
domain 0 runs an arithmetic + memory workload and halts; the other domains
halt immediately. Golden expectations live in `Tests/Lnp64u.lean`.
-/

namespace Machines.Lnp64u

open Loom Loom.Isa

/-- Assemble one instruction by mnemonic. -/
def ins (mn : String) (rd rs1 rs2 : RegId) (imm : BitVec 17) : Loom.Word32 :=
  match isa.findFinIdx? (·.mnemonic = mn) with
  | some i => encode isa i (mkOperands rd rs1 rs2 imm)
  | none => 0xffffffff  -- decodes to nothing: illegal-instruction fault

/-- Derive the trace events of one cycle. Recomputes the same pure phase
functions `step` uses; tooling only, never on a trusted path. -/
def cycleEvents (m : Manifest) (σ : MachineState) : List Trace.Line :=
  let c := σ.cycle.toNat
  let σ₁ := refillPhase m σ
  -- core: a retirement this cycle?
  let coreEvs : List Trace.Line :=
    match σ₁.inflight with
    | some fl =>
        if fl.cyclesLeft ≤ 1 then
          [{ cycle := c, event := .retire fl.dom.val (σ₁.doms fl.dom).pc.toNat
                                    fl.word.toNat }]
        else []
    | none => []
  let σ₂ := corePhase m σ₁
  -- halts: run flipped to halted during the core phase
  let haltEvs : List Trace.Line :=
    (List.finRange numDomains).filterMap fun d =>
      if (σ₁.doms d).run ≠ .halted ∧ (σ₂.doms d).run = .halted then
        some { cycle := c, event := .halt d.val (σ₂.doms d).cause.toNat }
      else none
  -- Mover: one word moved, a status write, or both
  let movEvs : List Trace.Line :=
    match σ₂.mover with
    | none => []
    | some job =>
        if job.remaining = 0 then
          [{ cycle := c, event := .status job.statusAddr.toNat 1 }]
        else if moverCheck σ₂ job.src job.srcCur { r := true, w := false, x := false } &&
                moverCheck σ₂ job.dst job.dstCur { r := false, w := true, x := false } then
          { cycle := c, event := .dma job.srcCur.toNat job.dstCur.toNat } ::
          (if job.remaining = 1
           then [{ cycle := c, event := .status job.statusAddr.toNat 1 }] else [])
        else
          [{ cycle := c, event := .status job.statusAddr.toNat
              Errno.staleHandle.toWord.toNat }]
  coreEvs ++ haltEvs ++ movEvs

/-- Run `n` cycles, collecting the trace. -/
def runTraced (m : Manifest) : Nat → MachineState → MachineState × Array Trace.Line
  | 0, σ => (σ, #[])
  | n + 1, σ =>
      let evs := (cycleEvents m σ).toArray
      let (σ', rest) := runTraced m n (step m σ)
      (σ', evs ++ rest)

/-- Run `n` cycles (no trace). -/
abbrev run (m : Manifest) : Nat → MachineState → MachineState := stepN m

/-! ## The golden demo configuration -/

/-- Build a ROM from a base address and word list (rest zero). -/
def romOf (chunks : List (Nat × List Loom.Word32)) : Addr → Loom.Word32 :=
  fun a =>
    chunks.foldr (init := 0) fun (base, ws) acc =>
      if base ≤ a.toNat ∧ a.toNat < base + ws.length
      then ws.getD (a.toNat - base) 0 else acc

/-- Domain `d`'s code region starts here (16 words each). -/
def codeBase (d : Nat) : Nat := 16 * d
/-- Domain `d`'s data region starts here (16 words each). -/
def dataBase (d : Nat) : Nat := 1024 + 16 * d

/-- Domain 0's demo program: compute 5 + 7, store, load back, halt.
Addressing is data-region-relative via `r7` = data base. -/
def demoProg0 : List Loom.Word32 :=
  [ ins "addi" 1 0 0 5                                -- r1 := 5
  , ins "addi" 2 0 0 7                                -- r2 := 7
  , ins "add"  3 1 2 0                                -- r3 := 12
  , ins "addi" 7 0 0 (BitVec.ofNat 17 (dataBase 0))   -- r7 := data base
  , ins "sw"   0 7 3 0                                -- mem[r7] := r3
  , ins "lw"   4 7 0 0                                -- r4 := mem[r7]
  , ins "halt" 0 0 0 0 ]

/-- The golden manifest: domain 0 runs `demoProg0`; domains 1–3 halt at
entry. Each domain boots with its code capability (r+x) in slot 0 mapped
into region 0, and a data capability (r+w) in slot 1 mapped into region 1.
Σ Q/P = 4 × 8/32 = 1. -/
def demoManifest : Manifest where
  doms := fun d =>
    { priority := numDomains - d.val   -- domain 0 highest
      budgetQ := 8
      periodP := 32
      entry := BitVec.ofNat 12 (codeBase d.val)
      initCaps := fun s =>
        if s = (0 : Fin numSlots) then
          some (.mem (BitVec.ofNat 12 (codeBase d.val)) 16
                     { r := true, w := false, x := true })
        else if s = (1 : Fin numSlots) then
          some (.mem (BitVec.ofNat 12 (dataBase d.val)) 16
                     { r := true, w := true, x := false })
        else none
      initRegions := fun r =>
        if r = (0 : Fin numRegions) then some 0
        else if r = (1 : Fin numRegions) then some 1
        else none }
  gates := fun _ => { callee := 1, entry := BitVec.ofNat 12 (codeBase 1) }
  rom := romOf
    [ (codeBase 0, demoProg0)
    , (codeBase 1, [ins "halt" 0 0 0 0])
    , (codeBase 2, [ins "halt" 0 0 0 0])
    , (codeBase 3, [ins "halt" 0 0 0 0]) ]

/-- Boot and run the demo to quiescence (all four domains halt well inside
200 cycles). -/
def demoResult : MachineState × Array Trace.Line :=
  runTraced demoManifest 200 demoManifest.initState

end Machines.Lnp64u
