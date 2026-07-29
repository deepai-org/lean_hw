-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

import Loom.Core.Fun
import Loom.Core.Word
import Loom.Core.Ts
import Loom.Core.Trace
import Loom.Isa.Decode
import Loom.Isa.Dsl
import Loom.Dp.Cert.Lrat
import Loom.Dp.Cert.Check
import Loom.Dp.Cnf
import Loom.Dp.Bmc
import Loom.Dp.Solver
import Loom.Dp.KInduction
import Loom.Book.Extract
import Loom.Book.Render.Html
import Loom.Emit.MicroVerilog.Semantics
import Loom.Hw.Semantics
import Loom.Hw.Compile
import Loom.Hw.CompileWhole
import Loom.Hw.WholeRegisterPlan
import Loom.Release.WholeRegisterPlan
import Loom.Hw.CompileCorrect
import Loom.Hw.ArtifactCert
import Loom.Release.Rope
import Loom.Release.SSA
import Loom.Release.Certificate
import Loom.Release.NamedCertificate
import Loom.Release.SymbolicCertificate
import Loom.Release.SymbolicElaborate
import Loom.Release.Verified
import Loom.Release.SymbolicSound
import Loom.Release.SymbolicVerified
import Loom.Release.ToProgram
import Loom.Release.ToProgramLemmas
import Loom.Release.RopeLayout
import Loom.Release.FlattenWF
import Loom.Release.KeyInjective
import Loom.Release.ToProgramWellFormed
import Loom.Release.ToProgramBehavior
import Loom.Release.ReadsValidKernel
import Loom.Release.ToProgramDenotes
import Loom.Emit.MicroVerilog.MatchesSemantics
import Loom.Emit.MicroVerilog.Print
import Loom.Emit.MicroVerilog.Axiom
import Loom.Emit.MicroVerilog.Parse
import Loom.Emit.MicroVerilog.RoundTrip
import Loom.Logic.Sep.Bi
import Loom.Logic.StepIndex

/-!
# Loom

Public umbrella module for Loom's machine-independent hardware EDSL, semantics,
decision procedures, µVerilog boundary, and documentation support.
-/
