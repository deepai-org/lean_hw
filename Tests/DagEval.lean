-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.DagEval
import Loom.Hw.Diff
import Machines.Substrate.S0Blinky
import Machines.Substrate.S13Soak

namespace Tests.DagEval

open Loom.Hw

private def blinkyFast := Machines.Substrate.S0Blinky.design.elaborate
private def soakFast := Machines.Substrate.S13Soak.design.elaborate

/-- Five action roots consuming the same nontrivial expression. This is the
shape that made LNP64mini's preemption predicate explode under tree
evaluation; sharing must cross action/funnel roots, not merely deduplicate
within one expression. -/
private def fiveFunnels : FastDesign :=
  let shared : FExpr := .and (.reg 5) (.not 1 (.reg 6))
  { acts := #[.write 0 shared, .write 1 shared, .write 2 shared,
      .write 3 shared, .write 4 shared]
    slots := []
    nregs := 7
    memTotal := 0
    names := #[
      ("out0", 1), ("out1", 1), ("out2", 1), ("out3", 1), ("out4", 1),
      ("guard", 1), ("block", 1)] }

/-- Independent construction plus structural certification succeeds on two
different designs. These are executable checks of the same gate LNP64mini
uses before entering the DAG evaluator. -/
example : (DagEval.prepare? blinkyFast).isSome = true := by native_decide
example : (DagEval.prepare? soakFast).isSome = true := by native_decide

/-- Structural reporting is definitionally tied to the graph it describes,
and the soak design exercises real sharing rather than a zero-only report. -/
example (fd : FastDesign) (d : DagEval.Design) :
    (DagEval.statsOf fd d).dagNodes = d.nodes.size := rfl

example : (DagEval.stats soakFast).dagNodes < (DagEval.stats soakFast).treeNodes := by
  native_decide

example : 0 < (DagEval.stats soakFast).maxDepth := by native_decide
example : 1 < (DagEval.stats soakFast).maxUses := by native_decide

/-- Cross-funnel regression: the shared subtree occurs five times in the
source trees but has one DAG root with five consumers. -/
example : (DagEval.stats fiveFunnels).treeNodes = 20 := by native_decide
example : (DagEval.stats fiveFunnels).dagNodes = 4 := by native_decide
example : (DagEval.stats fiveFunnels).maxUses = 5 := by native_decide
example : (DagEval.prepare? fiveFunnels).isSome = true := by native_decide

/-! Typed state views resolve declaration handles once and reject both stale
names and stale widths.  Their read theorem composes directly with the same
`Agree` relation used by the universal simulator proof. -/

example :
    (FastEval.regSlot? Machines.Substrate.S0Blinky.design
      Machines.Substrate.S0Blinky.cntReg).isSome = true := by
  native_decide

example :
    (FastEval.regSlot? Machines.Substrate.S0Blinky.design
      (⟨"cnt"⟩ : Reg 27)).isNone = true := by
  native_decide

example {fs : FastSt} {sigma : St}
    (slot : FastEval.RegSlot Machines.Substrate.S0Blinky.design
      Machines.Substrate.S0Blinky.cntReg)
    (ha : Agree Machines.Substrate.S0Blinky.design fs sigma) :
    slot.readNat fs =
      (sigma.regs Machines.Substrate.S0Blinky.cntReg.name 28).toNat :=
  slot.readNat_eq ha

/-- The executable comparison plan is derived from exactly the coordinates it
will cover; default comparison cannot silently accept a shorter plan. -/
example :
    (Machines.Substrate.S0Blinky.design.coordPlan? 8).map Array.size =
      some (Machines.Substrate.S0Blinky.design.coords 8).length := by
  native_decide

/-- A malformed lowering fails closed rather than becoming an executable
view. Emptying the node table leaves action roots dangling. -/
private def malformed : DagEval.Design :=
  { DagEval.lower blinkyFast with nodes := #[] }

example : (DagEval.checkCertificate blinkyFast malformed).isNone = true := by
  native_decide

/-- The public theorem is state/input-general, not a trace test. -/
example (dag : DagEval.Verified blinkyFast) (ι : InEnv) (fs : FastSt) :
    dag.cycleOpen ι fs = fastCycleOpen blinkyFast ι fs :=
  dag.cycleOpen_eq ι fs

/-- The design-level package composes the DAG certificate with the existing
`FastEval` proof, exposing the semantic theorem clients actually need. -/
example (sim : DagEval.VerifiedSimulator Machines.Substrate.S0Blinky.design)
    (ι : InEnv) (fs : FastSt) (σ : St)
    (ha : Agree Machines.Substrate.S0Blinky.design fs σ) :
    Agree Machines.Substrate.S0Blinky.design (sim.cycleOpen ι fs)
      (Machines.Substrate.S0Blinky.design.cycleOpen ι σ) :=
  sim.cycleOpen_eq ι fs σ ha

example (sim : DagEval.VerifiedSimulator Machines.Substrate.S0Blinky.design)
    (n : Nat) (ιs : Nat → InEnv) :
    Agree Machines.Substrate.S0Blinky.design
      (sim.runOpen ιs n sim.reset)
      (Machines.Substrate.S0Blinky.design.runOpen ιs n
        Machines.Substrate.S0Blinky.design.reset) :=
  sim.runOpenFromReset_eq n ιs

#print axioms Loom.Hw.DagEval.Verified.cycleOpen_eq
#print axioms Loom.Hw.DagEval.VerifiedSimulator.cycleOpen_eq
#print axioms Loom.Hw.DagEval.VerifiedSimulator.runOpenFromReset_eq
#print axioms Loom.Hw.FastEval.RegSlot.readNat_eq
#print axioms Loom.Hw.FastEval.MemSlot.readNat_eq

end Tests.DagEval
