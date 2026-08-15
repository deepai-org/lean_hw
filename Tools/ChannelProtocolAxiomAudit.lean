-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Multiclock

/-! Review surface for the compositional endpoint/progress layer. -/

#print axioms Loom.Hw.Chan.registeredTransfer_conservation
#print axioms Loom.Hw.Chan.runLedger_conservation
#print axioms Loom.Hw.System.RegisteredEndpointBinding.transfer_conservation
#print axioms Loom.Hw.System.RegisteredEndpointBinding.toEndpointCertificate
#print axioms Loom.Hw.System.ConnectionHandle.boundRegisteredSafety
#print axioms Loom.Hw.System.InterfaceProof.comp
#print axioms Loom.Hw.CertifiedSystem.runCompact_agrees
#print axioms Loom.Hw.TraceContract.BoundedService.comp
#print axioms Loom.Hw.TraceContract.BoundedService.parallel
