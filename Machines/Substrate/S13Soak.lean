-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Hw.Semantics
import Loom.Hw.FastEval
import Loom.Hw.DagEval
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

The certified generated evaluator runs the Design at full depth. In-repo
tests check its agreement with reference semantics and the soak's architectural
outcomes; emitted RTL and real ZC702 observations remain external evidence.
-/

namespace Machines.Substrate.S13Soak

open Loom.Hw

/-- Freeze point: the engine runs exactly this many cycles, then holds. -/
def K : Nat := 100000

def AGE_THRESH : Nat := 1500
def TMR_PERIOD : Nat := 300
def LFSR_INIT : Nat := 0xACE1

/-! ## Expression shorthands -/

def cycReg      : Reg 32 := ⟨"cyc"⟩
def lfsrReg     : Reg 16 := ⟨"lfsr"⟩
def ptrReg      : Reg 3  := ⟨"ptr"⟩
def tmrReg      : Reg 16 := ⟨"tmr"⟩
def dmaBusyReg  : Reg 1  := ⟨"dma_busy"⟩
def dmaCdReg    : Reg 4  := ⟨"dma_cd"⟩
def injectedReg : Reg 32 := ⟨"injected"⟩
def servicedReg : Reg 32 := ⟨"serviced"⟩
def errReg      : Reg 32 := ⟨"err"⟩
def maxoutReg   : Reg 32 := ⟨"maxout"⟩
def dmaSubReg   : Reg 32 := ⟨"dma_sub"⟩
def dmaCompReg  : Reg 32 := ⟨"dma_comp"⟩
def tmrExpReg   : Reg 32 := ⟨"tmr_exp"⟩
def pendRegs    : RegArray 1 8 := ⟨"pend"⟩
def ageRegs     : RegArray 11 8 := ⟨"age"⟩

def cyc      : Expr 32 := cycReg.rd
def lfsr     : Expr 16 := lfsrReg.rd
def ptr      : Expr 3  := ptrReg.rd
def tmr      : Expr 16 := tmrReg.rd
def dmaBusy  : Expr 1  := dmaBusyReg.rd
def dmaCd    : Expr 4  := dmaCdReg.rd
def injected : Expr 32 := injectedReg.rd
def serviced : Expr 32 := servicedReg.rd
def err      : Expr 32 := errReg.rd
def maxout   : Expr 32 := maxoutReg.rd
def dmaSub   : Expr 32 := dmaSubReg.rd
def dmaComp  : Expr 32 := dmaCompReg.rd
def tmrExp   : Expr 32 := tmrExpReg.rd
def pend (i : Fin 8) : Expr 1 := pendRegs.rd i
def age (i : Fin 8) : Expr 11 := ageRegs.rd i

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

def tickRule : Rule := ⟨"tick", guard (cycReg.set (.add cyc (.lit 1)))⟩

def lfsrRule : Rule :=
  ⟨"lfsr", guard (lfsrReg.set (.or (.shl lfsr (.lit 1)) (.zext fb 16)))⟩

def ptrRule : Rule := ⟨"ptr", guard (ptrReg.set (.add ptr (.lit 1)))⟩

/-- Round-robin server: drain source `i` if the pointer rests on it. -/
def serverRule (i : Fin 8) : Rule :=
  ⟨s!"server{i.val}", guard <|
    .ite (.and (.eq ptr (.lit (BitVec.ofNat 3 i.val))) (pend i))
      (.seq (pendRegs.set i (.lit 0))
            (servicedReg.set (.add serviced (.lit 1))))
      .skip⟩

/-- Random event injection into source `i` (coalesces if already pending). -/
def injectRule (i : Fin 8) : Rule :=
  ⟨s!"inject{i.val}", guard <|
    .ite (.and injFire (.eq isrc (.lit (BitVec.ofNat 3 i.val))))
      (.seq (pendRegs.set i (.lit 1))
            (ageRegs.set i (.lit 0)))
      .skip⟩

/-- Periodic timer: count, and inject on source 6 at each expiry. -/
def timerRule : Rule :=
  ⟨"timer", guard <|
    .seq (tmrReg.set (.mux tmrHit (.lit 0) (.add tmr (.lit 1))))
      (.seq (.ite tmrHit (tmrExpReg.set (.add tmrExp (.lit 1))) .skip)
        (.ite tmrInj
          (.seq (pendRegs.set 6 (.lit 1)) (ageRegs.set 6 (.lit 0)))
          .skip))⟩

/-- Conserved injection accounting: one add for both inject paths. -/
def injectedRule : Rule :=
  ⟨"injected", guard <|
    injectedReg.set (.add injected (.add (.zext injFire 32) (.zext tmrInj 32)))⟩

/-- DMA: submit when idle on `lfsr[9:7] == 3'b101`; complete after countdown. -/
def dmaRule : Rule :=
  ⟨"dma", guard <|
    .ite (.and (.not dmaBusy) (.eq (.slice lfsr 7 3) (.lit 0b101)))
      (.seq (dmaBusyReg.set (.lit 1))
        (.seq (dmaCdReg.set (.lit 8))
              (dmaSubReg.set (.add dmaSub (.lit 1)))))
      (.ite dmaBusy
        (.ite (.eq dmaCd (.lit 0))
          (.seq (dmaBusyReg.set (.lit 0))
                (dmaCompReg.set (.add dmaComp (.lit 1))))
          (dmaCdReg.set (.sub dmaCd (.lit 1))))
        .skip)⟩

/-- Age pending source `i`; a source aged past threshold is a LOST WAKEUP. -/
def agingRule (i : Fin 8) : Rule :=
  ⟨s!"aging{i.val}", guard <|
    .ite (pend i)
      (.ite (.ult (age i) (.lit (BitVec.ofNat 11 AGE_THRESH)))
        (ageRegs.set i (.add (age i) (.lit 1)))
        (.seq (errReg.set (.add err (.lit 1)))
              (pendRegs.set i (.lit 0))))
      .skip⟩

/-- Accounting invariants: never over-service, never over-complete. -/
def acctRule : Rule :=
  ⟨"acct", guard <|
    .seq (.ite (.ult injected serviced) (errReg.set (.add err (.lit 1))) .skip)
         (.ite (.ult dmaSub dmaComp) (errReg.set (.add err (.lit 1))) .skip)⟩

def maxoutRule : Rule :=
  ⟨"maxout", guard (.ite (.ult maxout popc32) (maxoutReg.set popc32) .skip)⟩

/-- Complete state and observability derived from the typed handles. -/
def declarations : Declarations :=
  Declarations.empty
    |>.addReg cycReg (exported := true)
    |>.addReg lfsrReg (BitVec.ofNat 16 LFSR_INIT) (exported := true)
    |>.addReg ptrReg (exported := true)
    |>.addReg tmrReg (exported := true)
    |>.addReg dmaBusyReg (exported := true)
    |>.addReg dmaCdReg (exported := true)
    |>.addReg injectedReg (exported := true)
    |>.addReg servicedReg (exported := true)
    |>.addReg errReg (exported := true)
    |>.addReg maxoutReg (exported := true)
    |>.addReg dmaSubReg (exported := true)
    |>.addReg dmaCompReg (exported := true)
    |>.addReg tmrExpReg (exported := true)
    |>.addRegArray pendRegs (exported := true)
    |>.addRegArray ageRegs (exported := true)

def s13Regs : List RegDecl := declarations.regs

def design : Design :=
  Design.ofDecls "s13soak" declarations <|
    [tickRule, lfsrRule, ptrRule]
    ++ (List.finRange 8).map serverRule
    ++ (List.finRange 8).map injectRule
    ++ [timerRule, injectedRule, dmaRule]
    ++ (List.finRange 8).map agingRule
    ++ [acctRule, maxoutRule]

/-! ## Generated execution, checks, and emission -/

/-- The FastEval side condition, discharged in the kernel — so
`Loom.Hw.FastEval.fastRun_eq` applies: the numbers `fastAt K` prints are a
*theorem* about `Design.run`, not just a corroborated computation. -/
theorem design_fastWF : design.fastWFB = true := by rfl

/-- The generated evaluator packaged with its semantic-equality proof. -/
def simulator : FastEval.VerifiedSimulator design := ⟨design_fastWF⟩

/-- The instantiated theorem: the fast state after `n` cycles agrees with
`design.run n design.reset` on every declared coordinate. -/
theorem fastRun_agrees (n : Nat) :
    Agree design (simulator.run n simulator.reset)
      (design.run n design.reset) :=
  simulator.runFromReset_eq n

/-- Every successfully prepared DAG instance carries the same run theorem;
preparation is checked at the executable boundary rather than justified by a
trusted native-decision proof. -/
theorem dagRun_agrees (dag : DagEval.VerifiedSimulator design) (n : Nat) :
    Agree design (dag.run n dag.reset) (design.run n design.reset) :=
  dag.runFromReset_eq n

/-- The elaborated design: names resolved to indices, once. -/
def fast : FastDesign := simulator.fast

/-- `fastCycle`-evaluated state after `n` cycles from reset. -/
def fastAt (n : Nat) : FastSt := simulator.run n simulator.reset

/-- Evaluate a long trace with a previously certified DAG. -/
def dagAt (dag : DagEval.VerifiedSimulator design) (n : Nat) : FastSt :=
  dag.run n dag.reset

def fastLookup (fs : FastSt) (n : String) : Option Nat :=
  (design.fastRegs fs).lookup n

/-- `fastCycle` ≡ the reference `Design.cycle` at a depth the *reference*
can still reach — the corroboration half of the FastEval story (the proved
half is `Loom.Hw.FastEval.fastCycle_eq`). -/
def refCheck (depth : Nat := 400) : IO Unit := do
  if ← design.lockstep depth then
    IO.println s!"S13SOAK REF LOCKSTEP OK ({depth} cycles, fastCycle ≡ Design.cycle)"
  else
    throw <| IO.userError "S13SOAK REF LOCKSTEP FAILED"

/-- Check the endurance run's architectural outcomes without restating its
transition function. The generated run is universally related to declarative
semantics by `dagRun_agrees`. -/
def outcomeCheck (depth : Nat := K + 8) : IO Unit := do
  let dag ← DagEval.prepareSimulator simulator "S13Soak"
  let fs := dagAt dag depth
  let frozen := dagAt dag K
  let read {w : Nat} (r : Reg w) := fastLookup fs r.name
  let outcomesOk :=
    match read cycReg, read errReg, read servicedReg, read injectedReg,
        read dmaCompReg, read dmaSubReg, read maxoutReg with
    | some cyc, some err, some serviced, some injected,
        some completed, some submitted, some maxout =>
      decide (cyc = K ∧ err = 0 ∧ serviced ≤ injected ∧
        completed ≤ submitted ∧ maxout ≤ 8 ∧
        design.fastRegs fs = design.fastRegs frozen)
    | _, _, _, _, _, _, _ => false
  if outcomesOk then
    IO.println s!"S13SOAK OUTCOME PASS depth={depth} (frozen, error-free, accounting sound)"
  else
    throw <| IO.userError s!"S13SOAK OUTCOME FAIL depth={depth}"

/-- Reference agreement plus the full-depth architectural outcome check. -/
def selftest (depth : Nat := K + 8) : IO Unit := do
  refCheck
  outcomeCheck depth

/-- The silicon prediction: the frozen state after K cycles (and a few
extra guard evaluations — freezing is idempotent), as `name=value` lines,
straight out of the compiled EDSL spec via the verified fast evaluator. -/
def predict : IO Unit := do
  let dag ← DagEval.prepareSimulator simulator "S13Soak"
  let fs := dagAt dag (K + 8)
  for (n, v) in design.fastRegs fs do
    IO.println s!"{n}={v}"

/-- Emission entry (root `main` lives in `Machines/Substrate/Emit.lean`). -/
def emit : IO Unit := design.emit "rtl/s13soak.v"

end Machines.Substrate.S13Soak
