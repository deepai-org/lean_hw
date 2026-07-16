-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ArtifactCert

/-!
# Release-artifact certificate checker regressions

Small kernel-reduced instances exercise the local expression and register-fold
validators. Full release certificates use the same soundness theorems with
proof data generated from the emitted module.
-/

namespace Tests.ArtifactCert

open Loom.Hw
open Loom.Hw.ArtifactCert

private def sourceValue : Loom.Hw.Expr 8 :=
  .add (.reg 8 "r") (.lit 1)

private def suppliedValue : Loom.Emit.MicroVerilog.Expr 8 :=
  .add (.reg 8 "r") (.lit 1)

#guard compileExprMatches sourceValue suppliedValue

private def sourceAction : Act :=
  .seq (.write 8 "r" sourceValue)
    (.ite (.reg 1 "take") (.write 8 "r" (.lit 2)) .skip)

private def suppliedNext : Loom.Emit.MicroVerilog.Expr 8 :=
  .mux (.reg 1 "take") (.lit 2) suppliedValue

private def cert : NextRegCert 8 :=
  .seq suppliedValue .write (.ite .write .same)

#guard nextRegMatches "r" 8 sourceAction (.reg 8 "r") suppliedNext cert

example : suppliedNext =
    Compile.nextReg "r" 8 sourceAction (.reg 8 "r") :=
  nextRegMatches_sound "r" 8 sourceAction (.reg 8 "r") suppliedNext cert
    (by decide +kernel)

end Tests.ArtifactCert
