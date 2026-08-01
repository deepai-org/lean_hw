-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

import Machines.Acc8.Theorems.A1
import Machines.Acc8.Theorems.AR
import Machines.Acc8.Theorems.AEV
import Machines.Acc8.TextRoundTrip
import Machines.Acc8.Iss
import Machines.Acc8.DslRegression
import Machines.Acc8.Core
import Machines.Lnp64u.Theorems.Ledger
import Machines.Lnp64u.Theorems.DemoWitness
import Machines.Lnp64u.Theorems.ReleaseWF
import Machines.Lnp64u.Iss
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Logic.KernelLemmas
import Machines.Lnp64u.Logic.PhaseLemmas
import Machines.Lnp64u.Logic.ExecWf
import Machines.Lnp64u.Logic.BaseOpsWf
import Machines.Lnp64u.Logic.SystemOpsWf
import Machines.Lnp64u.Logic.Sep.Resource
import Machines.Tutorial.SatCounter
import Machines.Tutorial.SatCounterArtifact
import Machines.Substrate.S0Blinky
import Machines.Substrate.S13Soak
import Machines.Substrate.S0BscanRegs
import Machines.Substrate.RetimeDemo
import Machines.Substrate.S1Counters
import Machines.Epoch.Protocol
import Machines.Epoch.Bmc
import Machines.Epoch.Engine
import Machines.Epoch.EpochSoc
import Machines.Epoch.Bounded
import Machines.Epoch.Refines
import Machines.CapWalk.Protocol
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.Iss
import Machines.Lnp64mini.Harness
import Machines.Lnp64mini.HpMaster
import Machines.Lnp64mini.GpMaster
import Machines.Lnp64mini.HpArbiter
import Machines.Lnp64mini.Soc
import Machines.Lnp64mini.DualSoc

/-!
# Machines

Public umbrella module for the Acc8 pathfinder and LNP64-µ processor model,
including their specifications, implementations, and headline theorems.
-/
