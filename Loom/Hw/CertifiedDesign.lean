-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.DagEvalComplete
import Loom.Emit.MicroVerilog.Print

/-!
# Complete single-source Design package

`CertifiedDesign` packages the proof obligations behind the user-facing claim
that one `Design` supplies both the certified development simulator and the
proved µVerilog compilation.  The executable DAG and the structural compiler
remain derived views; the fields retain only the kernel facts needed to join
them.
-/

namespace Loom.Hw

/-- A source Design together with its certified shared-DAG simulator and exact
reference compiler result. -/
structure CertifiedDesign (design : Design) where
  designWF : Compile.DesignWF design
  simulator : DagEval.VerifiedSimulator design
  compiled : Loom.Emit.MicroVerilog.Module
  compiled_eq : compiled = Compile.compile design

namespace CertifiedDesign

/-- Canonical package constructor: compilation is derived, never supplied as
an independent machine description. -/
def of {design : Design} (designWF : Compile.DesignWF design)
    (simulator : DagEval.VerifiedSimulator design) : CertifiedDesign design :=
  { designWF, simulator, compiled := Compile.compile design, compiled_eq := rfl }

/-- Fully derived constructor from the two executable source checks. DAG
preparation has a generic completeness theorem, so accepted designs acquire a
certified shared evaluator without a design-specific runtime rejection path. -/
def ofChecks {design : Design}
    (compilerReady : Compile.designWFCheck design = true)
    (simulatorReady : design.fastWFB = true) : CertifiedDesign design :=
  let base : FastEval.VerifiedSimulator design := ⟨simulatorReady⟩
  let simulator := DagEval.verifiedSimulatorOfPreparation base
    (DagEval.prepareSimulator?_complete base)
  .of (Compile.designWFCheck_sound design compilerReady) simulator

/-- The canonical emitted Verilog text.  This is a projection of the packaged
compiler result, not a separately supplied artifact. -/
def renderedVerilog {design : Design} (cert : CertifiedDesign design) : String :=
  Loom.Emit.MicroVerilog.Print.print cert.compiled

/-- Canonical rendering of the proved compiled transition with explicit
clock-edge intent. -/
def renderedVerilogOn {design : Design} (_cert : CertifiedDesign design)
    (edge : Loom.ClockEdge) : String :=
  Loom.Emit.MicroVerilog.Print.print (Compile.compileForEdge design edge)

/-- The literal UTF-8 bytes of the canonical emitted Verilog text. -/
def renderedUTF8 {design : Design} (cert : CertifiedDesign design) : ByteArray :=
  cert.renderedVerilog.toUTF8

/-- The packaged rendered text is exactly the printer applied to the proved
compiler result. -/
theorem renderedVerilog_eq {design : Design} (cert : CertifiedDesign design) :
    cert.renderedVerilog =
      Loom.Emit.MicroVerilog.Print.print (Compile.compile design) := by
  simp only [renderedVerilog, cert.compiled_eq]

/-- Byte-level form of `renderedVerilog_eq`.  Publication certificates can
bind this derived byte array to a shipped file without introducing another
machine description. -/
theorem renderedUTF8_eq {design : Design} (cert : CertifiedDesign design) :
    cert.renderedUTF8 =
      (Loom.Emit.MicroVerilog.Print.print (Compile.compile design)).toUTF8 := by
  exact congrArg String.toUTF8 cert.renderedVerilog_eq

theorem compiledForEdgeCycle_eq {design : Design}
    (_cert : CertifiedDesign design) (edge : Loom.ClockEdge)
    (state : Loom.Emit.MicroVerilog.St) :
    (Compile.compileForEdge design edge).cycle state =
      (Compile.compile design).cycle state :=
  Compile.compileForEdge_cycle design edge state

/-- Every declared same-cycle output of the packaged design agrees with its
compiled port expression for arbitrary current inputs and pre-edge state. -/
theorem combOutput_eq {design : Design} (cert : CertifiedDesign design)
    (output : CombOutput) (_declared : output ∈ design.combOutputs)
    (input : InEnv) (state : St) :
    Compile.mvEval
        (Loom.Emit.MicroVerilog.St.setInputs (Compile.convSt state)
          cert.compiled.ins input)
        (Compile.compileExpr output.value) =
      design.evalCombOutput input state output := by
  rw [cert.compiled_eq]
  exact Compile.compileCombOutput_evalOpen design output input state

/-- One optimized cycle agrees with the source `Design` semantics. -/
theorem cycleOpen_eq {design : Design} (cert : CertifiedDesign design)
    (input : InEnv) (fast : FastSt) (state : St)
    (agree : Agree design fast state) :
    Agree design (cert.simulator.cycleOpen input fast)
      (design.cycleOpen input state) :=
  cert.simulator.cycleOpen_eq input fast state agree

/-- The exact compiled module also agrees on live synchronous-reset edges.
This is the generic bridge used when a System recovery coordinator resets an
otherwise ordinary clock island. -/
theorem compiledCycleOpenWithReset_eq {design : Design}
    (cert : CertifiedDesign design) (reset : Bool) (input : InEnv)
    (state : St) :
    Compile.forgetSt
        (cert.compiled.cycleOpenWithReset reset input (Compile.convSt state)) =
      design.cycleOpenWithReset reset input state := by
  rw [cert.compiled_eq]
  exact Compile.compile_cycleOpenWithReset design cert.designWF reset input state

/-- Every finite optimized run agrees with the source `Design` semantics. -/
theorem runOpen_eq {design : Design} (cert : CertifiedDesign design)
    (n : Nat) (inputs : Nat → InEnv) (fast : FastSt) (state : St)
    (agree : Agree design fast state) :
    Agree design (cert.simulator.runOpen inputs n fast)
      (design.runOpen inputs n state) :=
  cert.simulator.runOpen_eq n inputs fast state agree

/-- One open simulator cycle agrees directly with the packaged compiled
module on every source-declared coordinate. -/
theorem compiledCycleOpen_eq {design : Design} (cert : CertifiedDesign design)
    (ι : InEnv) (fs : FastSt) (state : Loom.Emit.MicroVerilog.St)
    (ha : DagEval.CompiledAgree design fs state) :
    DagEval.CompiledAgree design (cert.simulator.cycleOpen ι fs)
      (cert.compiled.cycleOpen ι state) := by
  rw [cert.compiled_eq]
  exact cert.simulator.compiledCycleOpen_eq cert.designWF ι fs state ha

/-- Every finite open simulator run agrees directly with the packaged
compiled module for arbitrary inputs and initially agreeing states. -/
theorem compiledRunOpen_eq {design : Design} (cert : CertifiedDesign design)
    (n : Nat) (ιs : Nat → InEnv) (fs : FastSt)
    (state : Loom.Emit.MicroVerilog.St)
    (ha : DagEval.CompiledAgree design fs state) :
    DagEval.CompiledAgree design (cert.simulator.runOpen ιs n fs)
      (cert.compiled.runOpen ιs n state) := by
  rw [cert.compiled_eq]
  exact cert.simulator.compiledRunOpen_eq cert.designWF n ιs fs state ha

end CertifiedDesign

end Loom.Hw
