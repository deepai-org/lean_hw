-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Multiclock

/-!
# Three-clock graceful-recovery acceptance design

This deliberately tiny active pipeline makes the middle island incident to
two independently clocked channels. Source, forwarding, and sink counters
keep both FIFOs busy, so the RTL regression requests recovery from a genuine
nonempty/nonzero-pointer epoch. The middle island may report recovery and
reset only after all four physical endpoint halves have completed.
-/

namespace Machines.Multiclock.RecoverySmoke

open Loom.Hw

def inputQueue : Chan 8 := ⟨"recovery_in", 4, .exchange⟩
def outputQueue : Chan 8 := ⟨"recovery_out", 4, .exchange⟩

def clockA : ClockHandle := .named "recovery_clk_a"
def clockB : ClockHandle := .named "recovery_clk_b"
def clockC : ClockHandle := .named "recovery_clk_c"

def produced : Reg 8 := ⟨"produced"⟩
def forwarded : Reg 8 := ⟨"forwarded"⟩
def consumed : Reg 8 := ⟨"consumed"⟩

def sourceDesign : Design :=
  Design.ofDecls "recovery_source_design"
    (Declarations.empty.addReg produced 1 true)
    [⟨"produce",
      .ite inputQueue.canEnq
        (.seq (inputQueue.enq produced.rd)
          (produced.set (.add produced.rd (.lit 1))))
        .skip⟩]

def centerDesign : Design :=
  Design.ofDecls "recovery_center_design"
    (Declarations.empty.addReg forwarded 0 true)
    [⟨"forward",
      .ite (.and inputQueue.canDeq outputQueue.canEnq)
        (.seq (outputQueue.enq inputQueue.deq)
          (.seq inputQueue.pop
            (forwarded.set (.add forwarded.rd (.lit 1)))))
        .skip⟩]

def sinkDesign : Design :=
  Design.ofDecls "recovery_sink_design"
    (Declarations.empty.addReg consumed 0 true)
    [⟨"consume",
      .ite outputQueue.canDeq
        (.seq outputQueue.pop
          (consumed.set (.add consumed.rd (.lit 1))))
        .skip⟩]

def sourceIsland : IslandHandle :=
  .named "recovery_source" sourceDesign clockA
def centerIsland : IslandHandle :=
  .named "recovery_center" centerDesign clockB
def sinkIsland : IslandHandle :=
  .named "recovery_sink" sinkDesign clockC

def inputRoute := inputQueue.between sourceIsland centerIsland
def outputRoute := outputQueue.between centerIsland sinkIsland

def builder : SystemBuilder :=
  System.empty
    |>.addIsland sourceIsland
    |>.addIsland centerIsland
    |>.addIsland sinkIsland
    |>.addChannel inputRoute
    |>.addChannel outputRoute
    |>.withClockRel .asynchronous
    |>.withIndependentReset

def system : System := builder.certify (by decide)

def application : System.Application system :=
  system.realizeWith RealizationPlan.recoveryPortable (by native_decide)

end Machines.Multiclock.RecoverySmoke
