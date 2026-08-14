-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tools.ReleaseCertGen
import Loom.Release.ToProgram

namespace Tests.NamedCertificate

open Loom.Hw
open Loom.Release
open Loom.Release.SSA

private def sourceReg : RegDecl :=
  { name := "r", width := 8, init := 0 }

private def design : Design :=
  { name := "named_demo", regs := [sourceReg], mems := [],
    rules := [{ name := "step", body := .write 8 "r" (.lit 1) }],
    outputs := ["r"] }

private def program : Program where
  name := "named_demo"
  regs := [{ name := "r", width := 8, init := 0, next := "n0" }]
  mems := []
  wires := .leaf [{ width := 8, name := "n0", rhs := .lit 8 1 }]
  outs := [{ name := "o_r", width := 8, value := "r" }]

private def cert : Named.ModuleCert design where
  regs := .cons ⟨.cons (some "n0") .write .nil⟩ .nil
  mems := .nil

#guard ssaNamedMatches design program cert
run_cmd do
  unless (Tools.ReleaseCertGen.synthesize design program).isSome do
    throwError "named whole-write certificate synthesis failed"

/-! Partial-register updates participate in both certificate families. The
action-wide check is intentionally synthesized from the compiler's own SSA
program so this also covers the accumulator-dependent insert graph. -/
private def sliceDesign : Design :=
  { name := "named_slice_demo", regs := [sourceReg], mems := [],
    rules := [{ name := "step", body :=
      .writeSlice 8 "r" 2 3 (by omega) (.lit 5#3) }],
    outputs := ["r"] }

private def sliceActionCert : Symbolic.ActionWide.ActionCert :=
  .writeSlice 0 (.wire 0)

/- A slice write must keep the incoming register live: unlike a whole write,
it cannot clear the continuation's needed bit merely because it executes on
every control-flow path. -/
#guard sliceActionCert.summary.possible == 1
#guard sliceActionCert.summary.definite == 0
#guard Symbolic.ActionWide.neededBitsBefore sliceActionCert.summary 1 == 1

run_cmd do
  unless (Tools.ReleaseCertGen.synthesize sliceDesign
      sliceDesign.toProgram).isSome do
    throwError "named partial-write certificate synthesis failed"

run_cmd do
  let passed :=
    match Tools.ReleaseCertGen.synthesizeActionWideRegisterCert sliceDesign
        sliceDesign.toProgram with
    | some [cert@(.writeSlice 0 _)] =>
        cert.summary.definite == 0 &&
          (Tools.ReleaseCertGen.actionWideRulesToLean sliceDesign.regs [cert]).isSome
    | _ => false
  unless passed do
    throwError "action-wide partial-write certificate synthesis failed"

example : ∃ module, program.elaborate = some module ∧
    module.toTSys = (Compile.compile design).toTSys :=
  ssaNamedMatches_behavior design program cert (by decide +kernel)

end Tests.NamedCertificate
