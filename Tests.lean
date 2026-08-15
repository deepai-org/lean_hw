-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

import Tests.Acc8
import Tests.Acc8Core
import Tests.Lnp64u
import Tests.Lnp64uCore
import Tests.Lnp64miniArithmetic
import Tests.WideMul
import Tests.DivRem
import Tests.Chan
import Tests.MulticlockApi
import Tests.ChannelProtocol
import Tests.ClockGauntlet
import Tests.SoCFabricGauntlet
import Tests.MultiPort
import Tests.MemTarget
import Tests.Outputs
import Tests.LratBench
import Tests.CheckBench
import Tests.Acc8Bmc
import Tests.ArtifactCert
import Tests.ParserBoundary
import Tests.ReleaseRope
import Tests.ReleaseSSA
import Tests.ReleaseCertificate
import Tests.NamedCertificate
import Tests.Notation
import Tests.PrettyDsl
import Tests.PrettyDslImport
import Tests.Packed
import Tests.DebugTap
import Tests.CycleSupport
import Tests.DagEval
import Tests.SimulationComp
import Tests.Component
import Tests.ExternalComponent
import Tests.Stream
import Tests.Bus
import Tests.Arithmetic
import Tests.Waveform
import Tests.Plugin
import Tests.MemoryPort
import Tests.RegisterMap
import Tests.Arbiter
import Tests.Pipeline
import Tests.TransformChain
import Tests.Fanout
import Tests.Runner
import Tests.ArtifactIdentity

/-!
# Tests

Umbrella module for kernel checks, executable regressions, decision-procedure
benchmarks, and concrete machine witnesses.
-/
