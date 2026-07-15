-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGrant

/-!
# R-MC mem_grant framing

Unchanged-domain and gate faces for the fully selected grant action.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 64000000

private theorem gPrefix_ne_dPrefix (a b : String) :
    "g" ++ a ≠ "d" ++ b := by
  intro h
  have h' := congrArg String.toList h
  have hg : "g".toList = ['g'] := by decide
  have hd : "d".toList = ['d'] := by decide
  simp [hg, hd] at h'

private theorem gPrefix_ne_ifv (a : String) : "g" ++ a ≠ "if_v" := by
  intro h
  have h' := congrArg String.toList h
  have hg : "g".toList = ['g'] := by decide
  have hi : "if_v".toList = ['i', 'f', '_', 'v'] := by decide
  simp [hg, hi] at h'

private theorem toString_string (s : String) : toString s = s := rfl

private theorem domReadNames_prefix (x : DomainId) (q : String × Nat)
    (hq : q ∈ domReadNames x) :
    ∃ suffix, q.1 = "d" ++ (toString x.val ++ suffix) := by
  rcases q with ⟨rn, w⟩
  simp [domReadNames, Hw.dreg, Hw.dpc, Hw.dcapV, Hw.dcapKind,
    Hw.dcapLinV, Hw.dcapLin, Hw.dgen, Hw.dcellV, Hw.dcellPar, Hw.drgnV,
    Hw.drgn, Hw.drun, Hw.drunG, Hw.dsrvV, Hw.dsrv, Hw.dcause, Hw.dbudget,
    Hw.dmaxdon, toString_string, String.append_assoc] at hq ⊢
  aesop

private theorem grantExplicit_read_notin_other (e t x : DomainId)
    (hxe : x ≠ e) (hxt : x ≠ t) (NS : Slot) (NL : LineageId) :
    ∀ q ∈ domReadNames x, q ∉ (grantExplicit e t NS NL).regWrites := by
  intro q hq
  obtain ⟨suffix, hsuffix⟩ := domReadNames_prefix x q hq
  rw [grantExplicit_writes]
  rcases q with ⟨rn, w⟩
  simp only at hsuffix
  subst rn
  simp [Hw.dcapV, Hw.dcapKind, Hw.dcapLinV, Hw.dcapLin, Hw.dcellV,
    Hw.dcellPar, Hw.dreg, Hw.dpc, toString_string, String.append_assoc,
    dPrefix_ne_ifv, domPrefix_ne x t hxt, domPrefix_ne x e hxe]

/-- A selected grant leaves every domain other than issuer and target
unchanged. -/
theorem absDom_grantExplicit_other (σ acc : Loom.Hw.St)
    (e t x : DomainId) (hxe : x ≠ e) (hxt : x ≠ t)
    (NS : Slot) (NL : LineageId) :
    Hw.absDom ((grantExplicit e t NS NL).run σ acc) x =
      Hw.absDom acc x := by
  apply absDom_congr
  intro q hq
  exact frame (grantExplicit_read_notin_other e t x hxe hxt NS NL q hq)
    σ acc

private theorem grantExplicit_gate_notin (e t : DomainId)
    (NS : Slot) (NL : LineageId) (g : GateId) :
    ∀ q ∈ gateReadNames g, q ∉ (grantExplicit e t NS NL).regWrites := by
  rw [grantExplicit_writes]
  simp [gateReadNames, Hw.gcallee, Hw.gentry, Hw.gactV, Hw.gcaller,
    Hw.gcallerRd, Hw.gspc, Hw.gssrvV, Hw.gssrv, Hw.gdepth, Hw.gdon,
    Hw.gsreg, Hw.dcapV, Hw.dcapKind, Hw.dcapLinV, Hw.dcapLin,
    Hw.dcellV, Hw.dcellPar, Hw.dreg, Hw.dpc, toString_string,
    String.append_assoc,
    gPrefix_ne_dPrefix,
    gPrefix_ne_ifv]

/-- A selected grant does not alter any gate record. -/
theorem absGate_grantExplicit (σ acc : Loom.Hw.St)
    (e t : DomainId) (NS : Slot) (NL : LineageId) (g : GateId) :
    Hw.absGate ((grantExplicit e t NS NL).run σ acc) g =
      Hw.absGate acc g := by
  apply absGate_congr
  intro q hq
  exact frame (grantExplicit_gate_notin e t NS NL g q hq) σ acc

end Machines.Lnp64u.Theorems.RMC
