import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Iss
import Std.Data.HashMap

/-!
# LNP64-µ lockstep: EDSL core vs the spec (task 1.11)

Runs `(core testManifest)` against `Step.step` for 256 cycles, comparing
`abs` of the hardware state with the spec state **every cycle**.

What is compared (per cycle, via `stateEq`): the *complete* architectural
state — cycle counter, all 4096 memory words, and for every domain the
register file, pc, cap table (entries + lineage links), slot generations,
lineage cells, region registers, run state, serving, cause, budget and
maxDonation; every gate's config and activation; the mover job; the
in-flight latch. Nothing is projected away.

The test manifest uses **base ops only** (the HW's system-op retirement is
a temporary halt), and covers: ALU ops, `lui`/`addi` constants, `lw`/`sw`
inside granted regions, taken/untaken branches, a countdown loop, `jalr`,
infinite spin loops, an intentional store fault (d2, `memoryAuthority`
retirement fault — pc must not advance), a fetch fault (d3 boots with no
region registers), budget-exhaustion scheduling rotation, stalls, and
period refill.

`canonHw` re-materializes the hardware register environment each cycle
(HashMap-backed) so the closure chains stay shallow — test-harness
plumbing only, pointwise identity on everything the design and `abs` read.
-/

namespace Tests.Lnp64uCore

open Machines.Lnp64u Machines.Lnp64u.Hw Loom.Hw

/-! ## The base-ops-only test manifest -/

/-- Domain 0: countdown-sum loop, store/load, ALU mix, spin. -/
private def prog0 : List Loom.Word32 :=
  [ ins "addi" 1 0 0 3                              --  0: r1 := 3 (counter)
  , ins "addi" 2 0 0 0                              --  1: r2 := 0 (sum)
  , ins "addi" 7 0 0 (BitVec.ofNat 17 (dataBase 0)) --  2: r7 := data base
  , ins "add"  2 2 1 0                              --  3: r2 := r2 + r1
  , ins "addi" 1 1 0 (-1)                           --  4: r1 := r1 - 1
  , ins "blt"  0 0 1 (-2)                           --  5: if 0 <s r1 goto 3
  , ins "sw"   0 7 2 0                              --  6: mem[r7] := r2 (= 6)
  , ins "lw"   3 7 0 0                              --  7: r3 := mem[r7]
  , ins "lui"  4 0 0 1                              --  8: r4 := 1 <<< 15
  , ins "shr"  5 4 1 0                              --  9: r5 := r4 >> (r1&31)
  , ins "xor"  6 3 5 0                              -- 10: r6 := r3 ^ r5
  , ins "sub"  6 6 5 0                              -- 11: r6 := r6 - r5 (= 6)
  , ins "and"  6 6 3 0                              -- 12: r6 := r6 & r3 (= 6)
  , ins "or"   6 6 4 0                              -- 13: r6 := r6 | r4
  , ins "sw"   0 7 6 1                              -- 14: mem[r7+1] := r6
  , ins "beq"  0 0 0 0 ]                            -- 15: spin

/-- Domain 1: constants, shift, store, `jalr` over a skipped word, spin. -/
private def prog1 : List Loom.Word32 :=
  [ ins "addi" 7 0 0 (BitVec.ofNat 17 (dataBase 1)) -- 0: r7 := data base
  , ins "lui"  1 0 0 2                              -- 1: r1 := 2 <<< 15
  , ins "addi" 2 0 0 4                              -- 2: r2 := 4
  , ins "shr"  3 1 2 0                              -- 3: r3 := r1 >> 4 = 4096
  , ins "sw"   0 7 3 0                              -- 4: mem[r7] := 4096
  , ins "jalr" 4 0 0 (BitVec.ofNat 17 (codeBase 1 + 7)) -- 5: r4 := 22, pc := 23
  , ins "add"  5 5 5 0                              -- 6: (skipped)
  , ins "beq"  0 0 0 0 ]                            -- 7: spin

/-- Domain 2: store without write authority — retirement fault. -/
private def prog2 : List Loom.Word32 :=
  [ ins "sw" 0 0 0 0 ]                              -- mem[0] := r0: fault

/-- Base-ops-only manifest. Priorities: d2 > d3 > d0 > d1, so the two
faulting domains halt first and d0/d1 then share the core. d3 boots with
no region registers, so its very first fetch faults. -/
def testManifest : Manifest where
  doms := fun d =>
    { priority := [2, 1, 4, 3].getD d.val 0
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
        if d = (3 : Fin numDomains) then none
        else if r = (0 : Fin numRegions) then some 0
        else if r = (1 : Fin numRegions) then some 1
        else none }
  gates := fun _ => { callee := 1, entry := BitVec.ofNat 12 (codeBase 1) }
  rom := romOf
    [ (codeBase 0, prog0), (codeBase 1, prog1), (codeBase 2, prog2) ]

/-! ## Full-state comparison -/

private def domEq (a b : DomainState) : Bool :=
  (List.finRange numRegs).all (fun r => a.regs r == b.regs r) &&
  a.pc == b.pc &&
  (List.finRange numSlots).all (fun s =>
    decide (a.caps s = b.caps s) && a.slotGen s == b.slotGen s) &&
  (List.finRange numLineage).all (fun l => decide (a.lineage l = b.lineage l)) &&
  (List.finRange numRegions).all (fun r => decide (a.regions r = b.regions r)) &&
  decide (a.run = b.run) && decide (a.serving = b.serving) &&
  a.cause == b.cause && a.budget == b.budget && a.maxDonation == b.maxDonation

private def actEq : Option Activation → Option Activation → Bool
  | none, none => true
  | some x, some y =>
      decide (x.caller = y.caller) && decide (x.callerRd = y.callerRd) &&
      (List.finRange numRegs).all (fun r => x.savedRegs r == y.savedRegs r) &&
      x.savedPc == y.savedPc && decide (x.savedServing = y.savedServing) &&
      x.depth == y.depth && x.donated == y.donated
  | _, _ => false

private def gateEq (a b : GateState) : Bool :=
  decide (a.config = b.config) && actEq a.act b.act

private def moverEq : Option MoverJob → Option MoverJob → Bool
  | none, none => true
  | some x, some y =>
      decide (x.owner = y.owner) && decide (x.src = y.src) &&
      decide (x.dst = y.dst) && x.srcCur == y.srcCur &&
      x.dstCur == y.dstCur && x.remaining == y.remaining &&
      x.statusAddr == y.statusAddr
  | _, _ => false

private def inflEq : Option InFlight → Option InFlight → Bool
  | none, none => true
  | some x, some y =>
      decide (x.dom = y.dom) && x.word == y.word && x.cyclesLeft == y.cyclesLeft
  | _, _ => false

/-- Complete architectural-state equality (all 4096 memory words). -/
private def stateEq (a b : MachineState) : Bool :=
  a.cycle == b.cycle &&
  (List.finRange numDomains).all (fun d => domEq (a.doms d) (b.doms d)) &&
  (List.finRange numGates).all (fun g => gateEq (a.gates g) (b.gates g)) &&
  moverEq a.mover b.mover && inflEq a.inflight b.inflight &&
  (List.range memWords).all (fun i =>
    a.mem (BitVec.ofNat 12 i) == b.mem (BitVec.ofNat 12 i))

/-! ## Lockstep driver -/

/-- Re-materialize the hardware state (registers into a HashMap, memory
into an array) so closure chains stay shallow. Pointwise identity on every
signal the design and `abs` read. -/
private def canonHw (σ : Loom.Hw.St) : Loom.Hw.St :=
  let rmap : Std.HashMap String ((w : Nat) × BitVec w) :=
    (regDecls testManifest).foldl
      (fun mp rd => mp.insert rd.name ⟨rd.width, σ.regs rd.name rd.width⟩) ∅
  let mimg : Array Loom.Word32 :=
    Array.ofFn (fun i : Fin memWords => σ.mems "mem" i.val 32)
  { regs := fun n w =>
      match rmap.get? n with
      | some ⟨w', v⟩ => if h : w' = w then v.cast h else 0
      | none => 0
    mems := fun n a w =>
      if h : n = "mem" ∧ w = 32 then (mimg[a]?.getD 0).cast h.2.symm
      else 0 }

/-- Run both sides `n` cycles; `some c` is the first divergent cycle. -/
private def lockstep (n : Nat) : Option Nat :=
  let dsg := Machines.Lnp64u.Hw.core testManifest
  let rec go : Nat → Nat → Loom.Hw.St → MachineState → Option Nat
    | _, 0, hw, sp => if stateEq (abs hw) sp then none else some 0
    | c, k + 1, hw, sp =>
        if stateEq (abs hw) sp then
          go (c + 1) k (canonHw (dsg.cycle hw)) (step testManifest sp)
        else some c
  go 0 n (canonHw dsg.reset) testManifest.initState

private def check (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"Lnp64u core test failed: {name}")

#eval do
  -- lockstep over 256 cycles = 8 refill periods
  match lockstep 256 with
  | some c => throw (IO.userError
      s!"Lnp64u core/spec lockstep diverged at cycle {c}")
  | none => pure ()
  -- golden expectations on the final spec state (guards against a test
  -- manifest that silently exercises nothing)
  let final := stepN testManifest 256 testManifest.initState
  check "d0 sum stored" (final.read (BitVec.ofNat 12 (dataBase 0)) == 6)
  check "d0 or-result stored"
    (final.read (BitVec.ofNat 12 (dataBase 0 + 1)) == (6 ||| (1 <<< 15)))
  check "d0 spinning" (decide ((final.doms 0).run = RunState.running) &&
    (final.doms 0).pc == BitVec.ofNat 12 (codeBase 0 + 15))
  check "d1 shifted value stored"
    (final.read (BitVec.ofNat 12 (dataBase 1)) == 4096)
  check "d1 jalr link" ((final.doms 1).reg 4 == BitVec.ofNat 32 (codeBase 1 + 6))
  check "d1 skipped the jalr shadow" ((final.doms 1).reg 5 == 0)
  check "d1 spinning" (decide ((final.doms 1).run = RunState.running) &&
    (final.doms 1).pc == BitVec.ofNat 12 (codeBase 1 + 7))
  check "d2 store-fault halted" (decide ((final.doms 2).run = RunState.halted) &&
    (final.doms 2).cause == BitVec.ofNat 32 Fault.memoryAuthority.code)
  check "d2 fault pc not advanced"
    ((final.doms 2).pc == BitVec.ofNat 12 (codeBase 2))
  check "d3 fetch-fault halted" (decide ((final.doms 3).run = RunState.halted) &&
    (final.doms 3).cause == BitVec.ofNat 32 Fault.memoryAuthority.code)
  IO.println "Lnp64u core/spec lockstep passed (256 cycles, full state)"

end Tests.Lnp64uCore
