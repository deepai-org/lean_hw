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
import Machines.Lnp64u.Iss
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Logic.KernelLemmas
import Machines.Lnp64u.Logic.PhaseLemmas
import Machines.Lnp64u.Logic.ExecWf
import Machines.Lnp64u.Logic.BaseOpsWf
import Machines.Lnp64u.Logic.SystemOpsWf
import Machines.Lnp64u.Logic.Sep.Resource

/-!
# Machines

Public umbrella module for the Acc8 pathfinder and LNP64-µ processor model,
including their specifications, implementations, and headline theorems.
-/
