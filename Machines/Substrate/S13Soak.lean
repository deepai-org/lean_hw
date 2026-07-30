-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.FastEval
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

/-!
# S13Soak — the substrate-0 endurance/concurrency soak engine, ported to Loom

Port of `remote-fpga fpga/substrate0/rtl/s13_regs.v` (the board-endurance
soak: one free-running engine whose LFSR randomizes the interleaving of
event injection into 8 IRQ sources, a periodic timer that also injects, a
DMA submit/complete countdown, and a round-robin server draining pending
sources — with in-fabric checkers that latch errors on lost wakeups, aging
past threshold, or accounting violations).

Differences from the Verilog original, both forced by Loom's discipline and
faithful to it:

* The original is started/reset over JTAG (`RUN` register). A Loom `Design`
  is closed, so the port is **self-timed**: every rule is guarded by
  `cyc < K`; the engine runs exactly `K` cycles from reset and freezes.
  The frozen state is read back over the (untrusted) BSCAN wrapper and
  compared bit-for-bit against this file's own Lean evaluation — the
  compiled spec is the reference simulator.

* The Verilog updates `pending[i]` with per-bit nonblocking assignments.
  A whole-register last-write-wins port would clobber concurrent bit
  updates, so `pending` is eight 1-bit registers (`pend0`..`pend7`) — the
  same per-bit commit discipline, spelled out. The per-index rules are
  built by mapping builders over `Fin 8`, the same way the LNP64-µ core is
  generated.

The D9 semantics (all reads pre-cycle, ordered rules, last write wins) is
exactly the original's NBA semantics, including the s13 subtleties: at most
one net `err` increment per cycle no matter how many checkers fire, and
injection coalescing reads the *pre-cycle* pending bit even while the
server drains it in the same cycle.

`SoakIss` is the fast executable mirror (the ISS): a structure of BitVecs
and a step function. `Design.run` at small K is cross-checked against it
in-repo (`selftest`); the emitted RTL is cross-checked at full K by
iverilog; the real ZC702 is cross-checked at full K over BSCAN. Refinement
proofs are deliberately not attempted yet.
-/

namespace Machines.Substrate.S13Soak

open Loom.Hw

/-- Freeze point: the engine runs exactly this many cycles, then holds. -/
def K : Nat := 100000

def AGE_THRESH : Nat := 1500
def TMR_PERIOD : Nat := 300
def LFSR_INIT : Nat := 0xACE1

/-! ## Expression shorthands -/

def cyc      : Expr 32 := .reg 32 "cyc"
def lfsr     : Expr 16 := .reg 16 "lfsr"
def ptr      : Expr 3  := .reg 3  "ptr"
def tmr      : Expr 16 := .reg 16 "tmr"
def dmaBusy  : Expr 1  := .reg 1  "dma_busy"
def dmaCd    : Expr 4  := .reg 4  "dma_cd"
def injected : Expr 32 := .reg 32 "injected"
def serviced : Expr 32 := .reg 32 "serviced"
def err      : Expr 32 := .reg 32 "err"
def maxout   : Expr 32 := .reg 32 "maxout"
def dmaSub   : Expr 32 := .reg 32 "dma_sub"
def dmaComp  : Expr 32 := .reg 32 "dma_comp"
def tmrExp   : Expr 32 := .reg 32 "tmr_exp"
def pend (i : Fin 8) : Expr 1  := .reg 1  s!"pend{i.val}"
def age  (i : Fin 8) : Expr 11 := .reg 11 s!"age{i.val}"

/-- Engine enable: `cyc < K` (self-timed run, then freeze). -/
def running : Expr 1 := .ult cyc (.lit (BitVec.ofNat 32 K))

def guard (a : Act) : Act := .ite running a .skip

/-- Random-injection source select: `lfsr[6:4]`. -/
def isrc : Expr 3 := .slice lfsr 4 3

/-- Pre-cycle `pending[isrc]` (dynamic bit select as a mux chain). -/
def pendAtIsrc : Expr 1 :=
  (List.finRange 8).foldr
    (fun i acc => .mux (.eq isrc (.lit (BitVec.ofNat 3 i.val))) (pend i) acc)
    (.lit 0)

/-- Random injection fires: `lfsr[3:0] == 0xA` and the source is idle. -/
def injFire : Expr 1 := .and (.eq (.slice lfsr 0 4) (.lit 0xA)) (.not pendAtIsrc)

/-- Did the random injection just target source 6 (timer must not double-count)? -/
def set6 : Expr 1 := .and injFire (.eq isrc (.lit 6))

def tmrHit : Expr 1 := .eq tmr (.lit (BitVec.ofNat 16 TMR_PERIOD))

/-- Timer injection fires: period hit, source 6 idle, not just set randomly. -/
def tmrInj : Expr 1 := .and tmrHit (.and (.not (pend 6)) (.not set6))

/-- LFSR feedback: taps 15, 13, 12, 10 (x16 + x14 + x13 + x11 + 1). -/
def fb : Expr 1 :=
  .xor (.xor (.slice lfsr 15 1) (.slice lfsr 13 1))
       (.xor (.slice lfsr 12 1) (.slice lfsr 10 1))

/-- Pre-cycle popcount of pending, at 32 bits. -/
def popc32 : Expr 32 :=
  (List.finRange 8).foldl (fun acc i => .add acc (.zext (pend i) 32)) (.lit 0)

/-! ## Rules (same order as the original always-block) -/

def tickRule : Rule := ⟨"tick", guard (.write 32 "cyc" (.add cyc (.lit 1)))⟩

def lfsrRule : Rule :=
  ⟨"lfsr", guard (.write 16 "lfsr" (.or (.shl lfsr (.lit 1)) (.zext fb 16)))⟩

def ptrRule : Rule := ⟨"ptr", guard (.write 3 "ptr" (.add ptr (.lit 1)))⟩

/-- Round-robin server: drain source `i` if the pointer rests on it. -/
def serverRule (i : Fin 8) : Rule :=
  ⟨s!"server{i.val}", guard <|
    .ite (.and (.eq ptr (.lit (BitVec.ofNat 3 i.val))) (pend i))
      (.seq (.write 1 s!"pend{i.val}" (.lit 0))
            (.write 32 "serviced" (.add serviced (.lit 1))))
      .skip⟩

/-- Random event injection into source `i` (coalesces if already pending). -/
def injectRule (i : Fin 8) : Rule :=
  ⟨s!"inject{i.val}", guard <|
    .ite (.and injFire (.eq isrc (.lit (BitVec.ofNat 3 i.val))))
      (.seq (.write 1 s!"pend{i.val}" (.lit 1))
            (.write 11 s!"age{i.val}" (.lit 0)))
      .skip⟩

/-- Periodic timer: count, and inject on source 6 at each expiry. -/
def timerRule : Rule :=
  ⟨"timer", guard <|
    .seq (.write 16 "tmr" (.mux tmrHit (.lit 0) (.add tmr (.lit 1))))
      (.seq (.ite tmrHit (.write 32 "tmr_exp" (.add tmrExp (.lit 1))) .skip)
        (.ite tmrInj
          (.seq (.write 1 "pend6" (.lit 1)) (.write 11 "age6" (.lit 0)))
          .skip))⟩

/-- Conserved injection accounting: one add for both inject paths. -/
def injectedRule : Rule :=
  ⟨"injected", guard <|
    .write 32 "injected"
      (.add injected (.add (.zext injFire 32) (.zext tmrInj 32)))⟩

/-- DMA: submit when idle on `lfsr[9:7] == 3'b101`; complete after countdown. -/
def dmaRule : Rule :=
  ⟨"dma", guard <|
    .ite (.and (.not dmaBusy) (.eq (.slice lfsr 7 3) (.lit 0b101)))
      (.seq (.write 1 "dma_busy" (.lit 1))
        (.seq (.write 4 "dma_cd" (.lit 8))
              (.write 32 "dma_sub" (.add dmaSub (.lit 1)))))
      (.ite dmaBusy
        (.ite (.eq dmaCd (.lit 0))
          (.seq (.write 1 "dma_busy" (.lit 0))
                (.write 32 "dma_comp" (.add dmaComp (.lit 1))))
          (.write 4 "dma_cd" (.sub dmaCd (.lit 1))))
        .skip)⟩

/-- Age pending source `i`; a source aged past threshold is a LOST WAKEUP. -/
def agingRule (i : Fin 8) : Rule :=
  ⟨s!"aging{i.val}", guard <|
    .ite (pend i)
      (.ite (.ult (age i) (.lit (BitVec.ofNat 11 AGE_THRESH)))
        (.write 11 s!"age{i.val}" (.add (age i) (.lit 1)))
        (.seq (.write 32 "err" (.add err (.lit 1)))
              (.write 1 s!"pend{i.val}" (.lit 0))))
      .skip⟩

/-- Accounting invariants: never over-service, never over-complete. -/
def acctRule : Rule :=
  ⟨"acct", guard <|
    .seq (.ite (.ult injected serviced) (.write 32 "err" (.add err (.lit 1))) .skip)
         (.ite (.ult dmaSub dmaComp)   (.write 32 "err" (.add err (.lit 1))) .skip)⟩

def maxoutRule : Rule :=
  ⟨"maxout", guard (.ite (.ult maxout popc32) (.write 32 "maxout" popc32) .skip)⟩

def design : Design where
  name := "s13soak"
  regs :=
    [⟨"cyc", 32, 0⟩, ⟨"lfsr", 16, BitVec.ofNat 16 LFSR_INIT⟩, ⟨"ptr", 3, 0⟩,
     ⟨"tmr", 16, 0⟩, ⟨"dma_busy", 1, 0⟩, ⟨"dma_cd", 4, 0⟩,
     ⟨"injected", 32, 0⟩, ⟨"serviced", 32, 0⟩, ⟨"err", 32, 0⟩,
     ⟨"maxout", 32, 0⟩, ⟨"dma_sub", 32, 0⟩, ⟨"dma_comp", 32, 0⟩,
     ⟨"tmr_exp", 32, 0⟩]
    ++ (List.finRange 8).map (fun i => ⟨s!"pend{i.val}", 1, 0⟩)
    ++ (List.finRange 8).map (fun i => ⟨s!"age{i.val}", 11, 0⟩)
  mems := []
  rules :=
    [tickRule, lfsrRule, ptrRule]
    ++ (List.finRange 8).map serverRule
    ++ (List.finRange 8).map injectRule
    ++ [timerRule, injectedRule, dmaRule]
    ++ (List.finRange 8).map agingRule
    ++ [acctRule, maxoutRule]

/-! ## The fast executable mirror (ISS) -/

structure SoakSt where
  cyc      : BitVec 32 := 0
  lfsr     : BitVec 16 := BitVec.ofNat 16 LFSR_INIT
  ptr      : BitVec 3  := 0
  tmr      : BitVec 16 := 0
  dmaBusy  : Bool      := false
  dmaCd    : BitVec 4  := 0
  injected : BitVec 32 := 0
  serviced : BitVec 32 := 0
  err      : BitVec 32 := 0
  maxout   : BitVec 32 := 0
  dmaSub   : BitVec 32 := 0
  dmaComp  : BitVec 32 := 0
  tmrExp   : BitVec 32 := 0
  pend     : BitVec 8  := 0
  age      : Vector (BitVec 11) 8 := Vector.replicate 8 0
  deriving Repr, DecidableEq

namespace SoakIss

/-- One engine cycle: every read is from `s` (the pre-cycle state), all
writes build `s'` — the same discipline as the Design and the Verilog. -/
def step (s : SoakSt) : SoakSt := Id.run do
  if ¬ s.cyc.ult (BitVec.ofNat 32 K) then return s   -- frozen
  let mut s' := s
  s' := { s' with cyc := s.cyc + 1 }
  let fb := (s.lfsr.extractLsb' 15 1) ^^^ (s.lfsr.extractLsb' 13 1)
        ^^^ (s.lfsr.extractLsb' 12 1) ^^^ (s.lfsr.extractLsb' 10 1)
  s' := { s' with lfsr := (s.lfsr <<< 1) ||| fb.setWidth 16 }
  s' := { s' with ptr := s.ptr + 1 }
  -- server: drain pending[ptr] (pre-cycle view)
  let pi := s.ptr.toNat
  if s.pend.getLsbD pi then
    s' := { s' with pend := s'.pend &&& ~~~(1#8 <<< pi),
                    serviced := s.serviced + 1 }
  -- random injection (coalescing, pre-cycle pending)
  let isrc := (s.lfsr.extractLsb' 4 3).toNat
  let injFire := s.lfsr.extractLsb' 0 4 = 0xA#4 ∧ ¬ s.pend.getLsbD isrc
  let set6 := injFire ∧ isrc = 6
  if injFire then
    s' := { s' with pend := s'.pend ||| (1#8 <<< isrc),
                    age := s'.age.set! isrc 0 }
  -- periodic timer -> inject on source 6
  let tmrHit := s.tmr = BitVec.ofNat 16 TMR_PERIOD
  let tmrInj := tmrHit ∧ ¬ s.pend.getLsbD 6 ∧ ¬ set6
  s' := { s' with tmr := if tmrHit then 0 else s.tmr + 1 }
  if tmrHit then s' := { s' with tmrExp := s.tmrExp + 1 }
  if tmrInj then
    s' := { s' with pend := s'.pend ||| (1#8 <<< 6), age := s'.age.set! 6 0 }
  -- conserved injection accounting
  s' := { s' with injected :=
    s.injected + (if injFire then 1 else 0) + (if tmrInj then 1 else 0) }
  -- DMA
  if ¬ s.dmaBusy ∧ s.lfsr.extractLsb' 7 3 = 0b101#3 then
    s' := { s' with dmaBusy := true, dmaCd := 8, dmaSub := s.dmaSub + 1 }
  else if s.dmaBusy then
    if s.dmaCd = 0 then
      s' := { s' with dmaBusy := false, dmaComp := s.dmaComp + 1 }
    else
      s' := { s' with dmaCd := s.dmaCd - 1 }
  -- aging (pre-cycle pending/age); at most one net err bump per cycle
  let mut errBump := false
  for i in List.finRange 8 do
    if s.pend.getLsbD i.val then
      if (s.age[i.val]'(i.isLt)).ult (BitVec.ofNat 11 AGE_THRESH) then
        s' := { s' with age := s'.age.set! i.val ((s.age[i.val]'(i.isLt)) + 1) }
      else
        errBump := true
        s' := { s' with pend := s'.pend &&& ~~~(1#8 <<< i.val) }
  -- accounting invariants
  if s.injected.ult s.serviced then errBump := true
  if s.dmaSub.ult s.dmaComp then errBump := true
  if errBump then s' := { s' with err := s.err + 1 }
  -- max outstanding (pre-cycle popcount)
  let popc := BitVec.ofNat 32 ((List.range 8).countP (s.pend.getLsbD ·))
  if s.maxout.ult popc then s' := { s' with maxout := popc }
  return s'

def run (n : Nat) (s : SoakSt := {}) : SoakSt := n.fold (fun _ _ s => step s) s

end SoakIss

/-! ## Cross-checks and emission -/

/-- Read the ISS state as the Design's register environment would print. -/
def issRegs (s : SoakSt) : List (String × Nat) :=
  [("cyc", s.cyc.toNat), ("lfsr", s.lfsr.toNat), ("ptr", s.ptr.toNat),
   ("tmr", s.tmr.toNat), ("dma_busy", if s.dmaBusy then 1 else 0),
   ("dma_cd", s.dmaCd.toNat), ("injected", s.injected.toNat),
   ("serviced", s.serviced.toNat), ("err", s.err.toNat),
   ("maxout", s.maxout.toNat), ("dma_sub", s.dmaSub.toNat),
   ("dma_comp", s.dmaComp.toNat), ("tmr_exp", s.tmrExp.toNat)]
  ++ (List.range 8).map (fun i => (s!"pend{i}", if s.pend.getLsbD i then 1 else 0))
  ++ (List.range 8).map (fun i => (s!"age{i}", (s.age[i]!).toNat))

/-! ### The fast evaluator is the oracle

`SoakIss` below is now redundant: the `Design` itself runs at full K through
`Loom.Hw.FastEval`.  It is kept as an independent second opinion, and
`fastVsIss` proves the two agree on **every register at the full K = 100000**
— i.e. the verified fast evaluator reproduces exactly the numbers that were
read back from ZC702 silicon. -/

/-- The FastEval side condition, discharged in the kernel — so
`Loom.Hw.FastEval.fastRun_eq` applies: the numbers `fastAt K` prints are a
*theorem* about `Design.run`, not just a corroborated computation. -/
theorem design_fastWF : design.fastWFB = true := by rfl

/-- The instantiated theorem: the fast state after `n` cycles agrees with
`design.run n design.reset` on every declared coordinate. -/
theorem fastRun_agrees (n : Nat) :
    Agree design (fastRun design.elaborate n design.fastReset)
      (design.run n design.reset) :=
  FastEval.fastRun_eq design design_fastWF n _ _ (FastEval.agree_fastReset design)

/-- The elaborated design: names resolved to indices, once. -/
def fast : FastDesign := design.elaborate

/-- `fastCycle`-evaluated state after `n` cycles from reset. -/
def fastAt (n : Nat) : FastSt := fastRun fast n design.fastReset

def fastLookup (fs : FastSt) (n : String) : Option Nat :=
  (design.fastRegs fs).lookup n

/-- `fastCycle` ≡ the reference `Design.cycle` at a depth the *reference*
can still reach — the corroboration half of the FastEval story (the proved
half is `Loom.Hw.FastEval.fastCycle_eq`). -/
def refCheck (depth : Nat := 400) : IO Unit := do
  if ← design.lockstep depth then
    IO.println s!"S13SOAK REF LOCKSTEP OK ({depth} cycles, fastCycle ≡ Design.cycle)"
  else
    IO.println "S13SOAK REF LOCKSTEP FAILED"

/-- The EDSL data itself, evaluated by `fastCycle`, against the hand ISS —
at the FULL K.  The old version capped this at 400 cycles because
`Design.run` is quadratic; that limitation is gone. -/
def fastVsIss (depth : Nat := K + 8) : IO Unit := do
  let fs := fastAt depth
  let iss := SoakIss.run depth
  let mut bad := 0
  for (n, v) in issRegs iss do
    match fastLookup fs n with
    | some dv =>
        if dv ≠ v then
          IO.println s!"MISMATCH {n}: fast={dv} iss={v}"
          bad := bad + 1
    | none =>
        IO.println s!"MISSING {n} in fast state"
        bad := bad + 1
  if bad = 0 then
    IO.println s!"S13SOAK FAST≡ISS OK depth={depth} (all {(issRegs iss).length} regs)"
  else
    IO.println s!"S13SOAK FAST≡ISS FAILED ({bad} regs)"

/-- Design-vs-ISS lockstep.  `depth` is unbounded now — the oracle is
`fastCycle`, not `Design.run`. -/
def selftest (depth : Nat := K + 8) : IO Unit := do
  refCheck
  fastVsIss depth

/-- The silicon prediction: the frozen state after K cycles (and a few
extra guard evaluations — freezing is idempotent), as `name=value` lines,
straight out of the compiled EDSL spec via the verified fast evaluator. -/
def predict : IO Unit := do
  let fs := fastAt (K + 8)
  for (n, v) in design.fastRegs fs do
    IO.println s!"{n}={v}"

/-- Emission entry (root `main` lives in `Machines/Substrate/Emit.lean`). -/
def emit : IO Unit := design.emit "rtl/s13soak.v"

end Machines.Substrate.S13Soak
