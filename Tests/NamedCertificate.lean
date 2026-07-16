-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Tools.ReleaseCertGen

namespace Tests.NamedCertificate

open Loom.Hw
open Loom.Release
open Loom.Release.SSA

private def sourceReg : RegDecl :=
  { name := "r", width := 8, init := 0 }

private def design : Design :=
  { name := "named_demo", regs := [sourceReg], mems := [],
    rules := [{ name := "step", body := .write 8 "r" (.lit 1) }] }

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
#eval (Tools.ReleaseCertGen.synthesize design program).isSome

example : ∃ module, program.elaborate = some module ∧
    module.toTSys = (Compile.compile design).toTSys :=
  ssaNamedMatches_behavior design program cert (by decide +kernel)

end Tests.NamedCertificate
