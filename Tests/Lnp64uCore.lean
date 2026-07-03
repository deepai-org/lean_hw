import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Hw.Demo
import Machines.Lnp64u.Iss
import Loom.Hw.Compile
import Std.Data.HashMap

/-!
# LNP64-µ lockstep: EDSL core vs the spec (task 1.11)

Runs `(core m)` against `Step.step` comparing `abs` of the hardware state
with the spec state **every cycle** — the *complete* architectural state
(cycle counter, all 4096 memory words, per-domain register files / pc /
cap tables / slot generations / lineage cells / region registers / run /
serving / cause / budget / maxDonation, every gate's config + activation,
the Mover job, the in-flight latch). Nothing is projected away.

Two configurations:

1. **Base ops** (`testManifest`, 256 cycles): ALU, constants, loads/stores,
   branches, `jalr`, store/fetch faults, budget rotation, stalls, refill.
2. **System ops** (`Demo.sysManifest`, 2000 cycles): every system opcode —
   dup/narrow (+ `-EPERMDENIED`/`-EOUTOFRANGE`/`-ESTALE` paths), drop
   (reparent *and* orphan branches, region sweep), a revoke of a derivation
   tree with a cross-domain grant that also aborts an in-flight Mover job
   (`-ESTALE` status write), `mem_grant`, `map`/`unmap`, gate call/return
   with capability transfer + reply (incl. a nested depth-2 call and the
   three-hop payer walk), donation drain → forced unwind, callee `halt`
   unwind, a completing Mover job (same-cycle final word + status),
   `-EMOVERBUSY`/`-EGATEBUSY`, `yield`. Golden final-state expectations
   guard against a manifest that silently exercises nothing.

Also checked at run time: the compiled design's write-port discipline
(`designTrace = [0, 1, 2]`, the `MemWriteWF` port condition) and register
name uniqueness (`Nodup`), the preconditions of the emission theorems.

`canonHw`/`canonSp` re-materialize both states each cycle (HashMap/Array
backed) so closure chains stay shallow — test-harness plumbing only,
pointwise identity on everything the design, `abs`, and `step` read.
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

/-- Which components diverge (`hw` vs `spec`) — the debugging report. -/
private def diffReport (a b : MachineState) : String :=
  let parts :=
    (if a.cycle != b.cycle then [s!"cycle {a.cycle}≠{b.cycle}"] else [])
    ++ ((List.finRange numDomains).filterMap fun d =>
        if !domEq (a.doms d) (b.doms d) then
          let x := a.doms d
          let y := b.doms d
          let sub :=
            (if !(List.finRange numRegs).all (fun r => x.regs r == y.regs r)
             then ["regs"] else [])
            ++ (if x.pc != y.pc then [s!"pc {x.pc.toNat}≠{y.pc.toNat}"] else [])
            ++ (if !(List.finRange numSlots).all (fun s =>
                  decide (x.caps s = y.caps s)) then ["caps"] else [])
            ++ (if !(List.finRange numSlots).all (fun s =>
                  x.slotGen s == y.slotGen s) then ["gens"] else [])
            ++ (if !(List.finRange numLineage).all (fun l =>
                  decide (x.lineage l = y.lineage l)) then ["lineage"] else [])
            ++ (if !(List.finRange numRegions).all (fun r =>
                  decide (x.regions r = y.regions r)) then ["regions"] else [])
            ++ (if x.run != y.run then ["run"] else [])
            ++ (if x.serving != y.serving then ["serving"] else [])
            ++ (if x.cause != y.cause then ["cause"] else [])
            ++ (if x.budget != y.budget then
                  [s!"budget {x.budget}≠{y.budget}"] else [])
          some s!"dom{d.val}({String.intercalate "," sub})"
        else none)
    ++ ((List.finRange numGates).filterMap fun g =>
        if !gateEq (a.gates g) (b.gates g) then some s!"gate{g.val}" else none)
    ++ (if !moverEq a.mover b.mover then ["mover"] else [])
    ++ (if !inflEq a.inflight b.inflight then ["inflight"] else [])
    ++ (match (List.range memWords).find? (fun i =>
          a.mem (BitVec.ofNat 12 i) != b.mem (BitVec.ofNat 12 i)) with
        | some i => [s!"mem[{i}] {(a.mem (BitVec.ofNat 12 i)).toNat}≠{(b.mem (BitVec.ofNat 12 i)).toNat}"]
        | none => [])
  String.intercalate ", " parts

/-! ## Lockstep driver -/

/-- Re-materialize the hardware state (registers into a HashMap, memory
into an array) so closure chains stay shallow. Pointwise identity on every
signal the design and `abs` read. -/
private def canonHw (m : Manifest) (σ : Loom.Hw.St) : Loom.Hw.St :=
  let rmap : Std.HashMap String ((w : Nat) × BitVec w) :=
    (regDecls m).foldl
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

/-- Re-materialize the spec state (`Fun.update` chains grow with every
write; over thousands of cycles reads become the bottleneck). Pointwise
identity. -/
private def canonDom (ds : DomainState) : DomainState :=
  let regs := Array.ofFn (fun r : Fin numRegs => ds.regs r)
  let caps := Array.ofFn (fun s : Fin numSlots => ds.caps s)
  let gens := Array.ofFn (fun s : Fin numSlots => ds.slotGen s)
  let lin := Array.ofFn (fun l : Fin numLineage => ds.lineage l)
  let rgn := Array.ofFn (fun r : Fin numRegions => ds.regions r)
  { ds with
    regs := fun r => regs[r.val]!
    caps := fun s => caps[s.val]!
    slotGen := fun s => gens[s.val]!
    lineage := fun l => lin[l.val]!
    regions := fun r => rgn[r.val]! }

private def canonSp (σ : MachineState) : MachineState :=
  let mem := Array.ofFn (fun i : Fin memWords => σ.mem (BitVec.ofNat 12 i.val))
  let d0 := canonDom (σ.doms 0)
  let d1 := canonDom (σ.doms 1)
  let d2 := canonDom (σ.doms 2)
  let d3 := canonDom (σ.doms 3)
  { σ with
    mem := fun a => mem[a.toNat]!
    doms := fun d =>
      if d.val = 0 then d0 else if d.val = 1 then d1
      else if d.val = 2 then d2 else d3 }

/-- Run both sides `n` cycles; `.error (c, report)` is the first
divergence, `.ok final` the final (canonicalized) spec state. -/
private def lockstep (m : Manifest) (n : Nat) :
    Except (Nat × String) MachineState :=
  let dsg := Machines.Lnp64u.Hw.core m
  let rec go : Nat → Nat → Loom.Hw.St → MachineState →
      Except (Nat × String) MachineState
    | c, 0, hw, sp =>
        if stateEq (abs hw) sp then .ok sp else .error (c, diffReport (abs hw) sp)
    | c, k + 1, hw, sp =>
        if stateEq (abs hw) sp then
          go (c + 1) k (canonHw m (dsg.cycle hw)) (canonSp (step m sp))
        else .error (c, diffReport (abs hw) sp)
  go 0 n (canonHw m dsg.reset) (canonSp m.initState)

private def check (name : String) (b : Bool) : IO Unit :=
  unless b do throw (IO.userError s!"Lnp64u core test failed: {name}")

/-! ## 1. Base-op lockstep (256 cycles = 8 refill periods) -/

#eval do
  let final ← match lockstep testManifest 256 with
  | .error (c, r) => throw (IO.userError
      s!"Lnp64u base lockstep diverged at cycle {c}: {r}")
  | .ok f => pure f
  -- golden expectations on the final spec state (guards against a test
  -- manifest that silently exercises nothing)
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
  IO.println "Lnp64u base-op lockstep passed (256 cycles, full state)"

/-! ## 2. System-op lockstep (2000 cycles; see module docstring) -/

#eval do
  -- compiled-design well-formedness (the emission theorems' preconditions):
  -- one syntactic memory write per port, ascending; distinct signal names
  let dsg := Machines.Lnp64u.Hw.core Demo.sysManifest
  check "designTrace = [0,1,2] (MemWriteWF ports)"
    (decide (Loom.Hw.Compile.designTrace dsg "mem" = [0, 1, 2]))
  let names := dsg.regs.map RegDecl.name
  let uniq : Std.HashMap String Unit :=
    names.foldl (fun mp n => mp.insert n ()) ∅
  check "register names Nodup" (uniq.size == names.length)
  let final ← match lockstep Demo.sysManifest 2000 with
  | .error (c, r) => throw (IO.userError
      s!"Lnp64u system lockstep diverged at cycle {c}: {r}")
  | .ok f => pure f
  -- golden expectations on the final spec state
  let rd (a : Nat) : Loom.Word32 := final.read (BitVec.ofNat 12 a)
  check "dup+map store" (rd 0x410 == 1234)
  check "stale handle errno" (rd 0x426 == Errno.staleHandle.toWord)
  check "permDenied errno" (rd 0x428 == Errno.permDenied.toWord)
  check "outOfRange errno" (rd 0x429 == Errno.outOfRange.toWord)
  check "gateBusy errno (self-callee)" (rd 0x42A == Errno.gateBusy.toWord)
  check "moverBusy errno" (rd 0x42B == Errno.moverBusy.toWord)
  check "gate reply readback" (rd 0x42C == 777)
  check "donation-drain unwind errno" (rd 0x42D == Errno.calleeFault.toWord)
  check "callee-halt unwind errno" (rd 0x42E == Errno.calleeFault.toWord)
  check "aborted mover status = -ESTALE" (rd 0x424 == Errno.staleHandle.toWord)
  check "completed mover status = 1" (rd 0x425 == 1)
  check "mover payload copied"
    (rd 0x480 == 111 && rd 0x481 == 222 && rd 0x482 == 333 && rd 0x483 == 444)
  check "callee wrote through transferred cap" (rd 0x440 == 777)
  check "d2 read through granted cap" (rd 0x520 == 48879)
  check "aborted mover ran partially" (rd 0x700 == 48879 && rd 0x7C7 == 0)
  check "mailbox handshake" (rd 0x500 == 1 && rd 0x501 == 1 && rd 0x502 == 1)
  check "d1 halted voluntarily (cause 0)"
    (decide ((final.doms 1).run = RunState.halted) && (final.doms 1).cause == 0)
  check "d2 halted on swept region (memoryAuthority)"
    (decide ((final.doms 2).run = RunState.halted) &&
     (final.doms 2).cause == BitVec.ofNat 32 Fault.memoryAuthority.code)
  check "d3 halted by donation drain (budget)"
    (decide ((final.doms 3).run = RunState.halted) &&
     (final.doms 3).cause == BitVec.ofNat 32 Fault.budget.code)
  check "d0 spinning at the end"
    (decide ((final.doms 0).run = RunState.running) &&
     (final.doms 0).pc == BitVec.ofNat 12 Demo.prog0Spin)
  IO.println "Lnp64u system-op lockstep passed (2000 cycles, full state)"

end Tests.Lnp64uCore
