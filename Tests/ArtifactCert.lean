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

private def rules : List Rule := [⟨"step", sourceAction⟩]

private def rulesCert : NextRulesCert 8 :=
  .cons suppliedNext cert .nil

#guard nextRulesMatches "r" 8 rules (.reg 8 "r") suppliedNext rulesCert

example : suppliedNext = rules.foldl
    (fun acc rl => Compile.nextReg "r" 8 rl.body acc) (.reg 8 "r") :=
  nextRulesMatches_sound "r" 8 rules (.reg 8 "r") suppliedNext rulesCert
    (by decide +kernel)

private def portStart : Compile.Port 4 8 :=
  { en := .lit 0, addr := .lit 0, data := .lit 0 }

private def memAction : Act :=
  .memWrite 4 8 "ram" 0 (.lit 3) sourceValue

private def suppliedPort : Compile.Port 4 8 :=
  { en := .lit 1, addr := .lit 3, data := suppliedValue }

#guard nextPortMatches "ram" 4 8 0 memAction portStart suppliedPort .write

example : suppliedPort = Compile.memPort "ram" 4 8 0 memAction portStart :=
  nextPortMatches_sound "ram" 4 8 0 memAction portStart suppliedPort .write
    (by decide +kernel)

private def memRules : List Rule := [⟨"store", memAction⟩]

private def portRulesCert : NextPortRulesCert 4 8 :=
  .cons suppliedPort .write .nil

#guard nextPortRulesMatches "ram" 4 8 0 memRules portStart suppliedPort
  portRulesCert

example : suppliedPort = memRules.foldl
    (fun acc rl => Compile.memPort "ram" 4 8 0 rl.body acc) portStart :=
  nextPortRulesMatches_sound "ram" 4 8 0 memRules portStart suppliedPort
    portRulesCert (by decide +kernel)

end Tests.ArtifactCert
