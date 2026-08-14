-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CertifiedDesign
import Loom.Hw.Declarations

/-!
# Compiler-produced recovery datapath guards

These combinational `Design`s are the only Boolean glue between a recovery
endpoint and the ordinary FIFO implementation. They deliberately expose no
clock-domain protocol of their own:

* the source guard masks `valid` and `ready` while its endpoint is quiesced;
* the sink guard masks `pop` and `valid` while its endpoint is quiesced; and
* each guard asserts the reset of only its local FIFO half on global reset or
  the endpoint's proved flush/reset-hold level.

Payload bits pass unchanged. A packed record therefore uses the same guard
after its one canonical packing operation.
-/

namespace Loom.Hw
namespace Chan.RecoveryDatapath

structure Parameters where
  width : Nat

def sourceValid : Reg 1 := ⟨"source_valid"⟩
def sourcePayload (p : Parameters) : Reg p.width := ⟨"source_payload"⟩
def fifoReady : Reg 1 := ⟨"fifo_ready"⟩
def sourceBlocked : Reg 1 := ⟨"recovery_blocked"⟩
def sourceFlush : Reg 1 := ⟨"recovery_flush"⟩
def sourceGlobalReset : Reg 1 := ⟨"global_reset"⟩

def sourceFifoValidExpr : Expr 1 :=
  .and sourceValid.rd (.not sourceBlocked.rd)
def sourceReadyExpr : Expr 1 :=
  .and fifoReady.rd (.not sourceBlocked.rd)
def sourceAcceptedExpr : Expr 1 :=
  .and sourceValid.rd sourceReadyExpr
def sourceFifoResetExpr : Expr 1 :=
  .or sourceGlobalReset.rd sourceFlush.rd

def sourceDesign (p : Parameters) : Design :=
  Design.ofDecls s!"channel_recovery_source_guard_w{p.width}"
    (Declarations.empty
      |>.addInput sourceValid
      |>.addInput (sourcePayload p)
      |>.addInput fifoReady
      |>.addInput sourceBlocked
      |>.addInput sourceFlush
      |>.addInput sourceGlobalReset
      |>.addCombOutput "fifo_valid" sourceFifoValidExpr
      |>.addCombOutput "fifo_payload" (sourcePayload p).rd
      |>.addCombOutput "source_ready" sourceReadyExpr
      |>.addCombOutput "source_accepted" sourceAcceptedExpr
      |>.addCombOutput "fifo_reset" sourceFifoResetExpr) []

def fifoValid : Reg 1 := ⟨"fifo_valid"⟩
def fifoPayload (p : Parameters) : Reg p.width := ⟨"fifo_payload"⟩
def sinkPop : Reg 1 := ⟨"sink_pop"⟩
def sinkBlocked : Reg 1 := ⟨"recovery_blocked"⟩
def sinkFlush : Reg 1 := ⟨"recovery_flush"⟩
def sinkGlobalReset : Reg 1 := ⟨"global_reset"⟩

def sinkFifoPopExpr : Expr 1 :=
  .and sinkPop.rd (.not sinkBlocked.rd)
def sinkValidExpr : Expr 1 :=
  .and fifoValid.rd (.not sinkBlocked.rd)
def sinkFifoResetExpr : Expr 1 :=
  .or sinkGlobalReset.rd sinkFlush.rd

def sinkDesign (p : Parameters) : Design :=
  Design.ofDecls s!"channel_recovery_sink_guard_w{p.width}"
    (Declarations.empty
      |>.addInput fifoValid
      |>.addInput (fifoPayload p)
      |>.addInput sinkPop
      |>.addInput sinkBlocked
      |>.addInput sinkFlush
      |>.addInput sinkGlobalReset
      |>.addCombOutput "fifo_pop" sinkFifoPopExpr
      |>.addCombOutput "sink_valid" sinkValidExpr
      |>.addCombOutput "sink_payload" (fifoPayload p).rd
      |>.addCombOutput "fifo_reset" sinkFifoResetExpr) []

def boolBit (value : Bool) : BitVec 1 := if value then 1#1 else 0#1

def sourceDrive (p : Parameters) (valid : Bool) (payload : BitVec p.width)
    (ready blocked flush globalReset : Bool) : InEnv :=
  fun name width =>
    if h : width = 1 then
      if name = sourceValid.name then h.symm ▸ boolBit valid
      else if name = fifoReady.name then h.symm ▸ boolBit ready
      else if name = sourceBlocked.name then h.symm ▸ boolBit blocked
      else if name = sourceFlush.name then h.symm ▸ boolBit flush
      else if name = sourceGlobalReset.name then h.symm ▸ boolBit globalReset
      else if payloadWidth : width = p.width then
        if name = (sourcePayload p).name then payloadWidth ▸ payload else 0#width
      else 0#width
    else if payloadWidth : width = p.width then
      if name = (sourcePayload p).name then payloadWidth ▸ payload else 0#width
    else 0#width

def sinkDrive (p : Parameters) (valid : Bool) (payload : BitVec p.width)
    (pop blocked flush globalReset : Bool) : InEnv :=
  fun name width =>
    if h : width = 1 then
      if name = fifoValid.name then h.symm ▸ boolBit valid
      else if name = sinkPop.name then h.symm ▸ boolBit pop
      else if name = sinkBlocked.name then h.symm ▸ boolBit blocked
      else if name = sinkFlush.name then h.symm ▸ boolBit flush
      else if name = sinkGlobalReset.name then h.symm ▸ boolBit globalReset
      else if payloadWidth : width = p.width then
        if name = (fifoPayload p).name then payloadWidth ▸ payload else 0#width
      else 0#width
    else if payloadWidth : width = p.width then
      if name = (fifoPayload p).name then payloadWidth ▸ payload else 0#width
    else 0#width

theorem source_fifoValid (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (ready blocked flush globalReset : Bool) :
    sourceFifoValidExpr.eval ((sourceDesign p).reset.setInputs
      (sourceDesign p).inputs
      (sourceDrive p valid payload ready blocked flush globalReset)) =
      boolBit (valid && !blocked) := by
  cases valid <;> cases ready <;> cases blocked <;> cases flush <;>
    cases globalReset <;>
    simp [sourceFifoValidExpr, sourceDesign, sourceDrive, boolBit,
      Design.reset, RegEnv.set, St.setInputs, Reg.rd, Reg.input, Expr.eval,
      sourceValid, sourcePayload, fifoReady, sourceBlocked, sourceFlush,
      sourceGlobalReset]

theorem source_payload (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (ready blocked flush globalReset : Bool) :
    (sourcePayload p).rd.eval ((sourceDesign p).reset.setInputs
      (sourceDesign p).inputs
      (sourceDrive p valid payload ready blocked flush globalReset)) =
      payload := by
  simp [sourceDesign, sourceDrive, Design.reset, RegEnv.set, St.setInputs,
    Reg.rd, Reg.input, Expr.eval, sourceValid, sourcePayload, fifoReady,
    sourceBlocked, sourceFlush, sourceGlobalReset]

theorem source_ready (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (ready blocked flush globalReset : Bool) :
    sourceReadyExpr.eval ((sourceDesign p).reset.setInputs
      (sourceDesign p).inputs
      (sourceDrive p valid payload ready blocked flush globalReset)) =
      boolBit (ready && !blocked) := by
  cases valid <;> cases ready <;> cases blocked <;> cases flush <;>
    cases globalReset <;>
    simp [sourceReadyExpr, sourceDesign, sourceDrive, boolBit,
      Design.reset, RegEnv.set, St.setInputs, Reg.rd, Reg.input, Expr.eval,
      sourceValid, sourcePayload, fifoReady, sourceBlocked, sourceFlush,
      sourceGlobalReset]

theorem source_accepted (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (ready blocked flush globalReset : Bool) :
    sourceAcceptedExpr.eval ((sourceDesign p).reset.setInputs
      (sourceDesign p).inputs
      (sourceDrive p valid payload ready blocked flush globalReset)) =
      boolBit (valid && ready && !blocked) := by
  cases valid <;> cases ready <;> cases blocked <;> cases flush <;>
    cases globalReset <;>
    simp [sourceAcceptedExpr, sourceReadyExpr, sourceDesign, sourceDrive,
      boolBit, Design.reset, RegEnv.set, St.setInputs, Reg.rd, Reg.input,
      Expr.eval, sourceValid, sourcePayload, fifoReady, sourceBlocked,
      sourceFlush, sourceGlobalReset]

theorem source_fifoReset (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (ready blocked flush globalReset : Bool) :
    sourceFifoResetExpr.eval ((sourceDesign p).reset.setInputs
      (sourceDesign p).inputs
      (sourceDrive p valid payload ready blocked flush globalReset)) =
      boolBit (globalReset || flush) := by
  cases valid <;> cases ready <;> cases blocked <;> cases flush <;>
    cases globalReset <;>
    simp [sourceFifoResetExpr, sourceDesign, sourceDrive, boolBit,
      Design.reset, RegEnv.set, St.setInputs, Reg.rd, Reg.input, Expr.eval,
      sourceValid, sourcePayload, fifoReady, sourceBlocked, sourceFlush,
      sourceGlobalReset]

theorem sink_fifoPop (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (pop blocked flush globalReset : Bool) :
    sinkFifoPopExpr.eval ((sinkDesign p).reset.setInputs (sinkDesign p).inputs
      (sinkDrive p valid payload pop blocked flush globalReset)) =
      boolBit (pop && !blocked) := by
  cases valid <;> cases pop <;> cases blocked <;> cases flush <;>
    cases globalReset <;>
    simp [sinkFifoPopExpr, sinkDesign, sinkDrive, boolBit,
      Design.reset, RegEnv.set, St.setInputs, Reg.rd, Reg.input, Expr.eval,
      fifoValid, fifoPayload, sinkPop, sinkBlocked, sinkFlush,
      sinkGlobalReset]

theorem sink_valid (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (pop blocked flush globalReset : Bool) :
    sinkValidExpr.eval ((sinkDesign p).reset.setInputs (sinkDesign p).inputs
      (sinkDrive p valid payload pop blocked flush globalReset)) =
      boolBit (valid && !blocked) := by
  cases valid <;> cases pop <;> cases blocked <;> cases flush <;>
    cases globalReset <;>
    simp [sinkValidExpr, sinkDesign, sinkDrive, boolBit,
      Design.reset, RegEnv.set, St.setInputs, Reg.rd, Reg.input, Expr.eval,
      fifoValid, fifoPayload, sinkPop, sinkBlocked, sinkFlush,
      sinkGlobalReset]

theorem sink_payload (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (pop blocked flush globalReset : Bool) :
    (fifoPayload p).rd.eval ((sinkDesign p).reset.setInputs
      (sinkDesign p).inputs
      (sinkDrive p valid payload pop blocked flush globalReset)) =
      payload := by
  simp [sinkDesign, sinkDrive, Design.reset, RegEnv.set, St.setInputs,
    Reg.rd, Reg.input, Expr.eval, fifoValid, fifoPayload, sinkPop,
    sinkBlocked, sinkFlush, sinkGlobalReset]

theorem sink_fifoReset (p : Parameters) (valid : Bool)
    (payload : BitVec p.width) (pop blocked flush globalReset : Bool) :
    sinkFifoResetExpr.eval ((sinkDesign p).reset.setInputs (sinkDesign p).inputs
      (sinkDrive p valid payload pop blocked flush globalReset)) =
      boolBit (globalReset || flush) := by
  cases valid <;> cases pop <;> cases blocked <;> cases flush <;>
    cases globalReset <;>
    simp [sinkFifoResetExpr, sinkDesign, sinkDrive, boolBit,
      Design.reset, RegEnv.set, St.setInputs, Reg.rd, Reg.input, Expr.eval,
      fifoValid, fifoPayload, sinkPop, sinkBlocked, sinkFlush,
      sinkGlobalReset]

def compilerReady (p : Parameters) : Bool :=
  Compile.designWFCheck (sourceDesign p) && (sourceDesign p).fastWFB &&
    Compile.designWFCheck (sinkDesign p) && (sinkDesign p).fastWFB

structure Certified (p : Parameters) where
  source : CertifiedDesign (sourceDesign p)
  sink : CertifiedDesign (sinkDesign p)

def certify (p : Parameters) (ready : compilerReady p = true) : Certified p := by
  simp only [compilerReady, Bool.and_eq_true_iff] at ready
  exact
    { source := CertifiedDesign.ofChecks ready.1.1.1 ready.1.1.2
      sink := CertifiedDesign.ofChecks ready.1.2 ready.2 }

end Chan.RecoveryDatapath
end Loom.Hw
