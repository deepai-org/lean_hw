-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CertifiedDesign
import Loom.Hw.Declarations

/-!
# Certified recovery-completion synchronizer

An island-level recovery gate consumes the completion of both physical halves
of every incident channel.  The remote half is a persistent handshake level,
but persistence alone is not metastability protection.  This ordinary
single-clock `Design` supplies the required two destination-domain stages so
the structural System renderer never feeds a raw remote completion into an
island's recovery/reset decision.
-/

namespace Loom.Hw.System.RecoveryCompletionSynchronizer

open Loom.Hw

def rawCompletion : Reg 1 := ⟨"raw_completion"⟩
def completionSync0 : Reg 1 := ⟨"completion_sync0"⟩
def completionSync1 : Reg 1 := ⟨"completion_sync1"⟩

def design : Design :=
  Design.ofDecls "system_recovery_completion_synchronizer"
    (Declarations.empty
      |>.addInput rawCompletion
      |>.addReg completionSync0
      |>.addReg completionSync1 0 true)
    [⟨"synchronize_completion",
      .seq (completionSync0.set rawCompletion.rd)
        (completionSync1.set completionSync0.rd)⟩]

def compilerReady : Bool :=
  Compile.designWFCheck design && design.fastWFB

theorem compilerReady_true : compilerReady = true := by decide

def certified : CertifiedDesign design := by
  have checks := Bool.and_eq_true_iff.mp compilerReady_true
  exact CertifiedDesign.ofChecks checks.1 checks.2

end Loom.Hw.System.RecoveryCompletionSynchronizer
