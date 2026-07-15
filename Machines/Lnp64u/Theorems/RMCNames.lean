-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Hw.BaseOps
import Loom.Hw.Compile
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-!
# R-MC register-name facts

Kernel-checked injectivity and disjointness facts for the architectural
register-name encoding.  Keeping these facts here prevents retirement proofs
from repeatedly enumerating the same finite string comparisons.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Machines.Lnp64u.Hw

theorem toString_string (s : String) : toString s = s := rfl

/-- Names carrying different architectural domain prefixes are disjoint. -/
theorem domPrefix_ne (x y : DomainId) (hxy : x ≠ y) (a b : String) :
    "d" ++ (toString x.val ++ a) ≠ "d" ++ (toString y.val ++ b) := by
  fin_cases x <;> fin_cases y
  all_goals first | exact absurd rfl hxy | skip
  all_goals
    intro h
    have h' := congrArg String.toList h
    have hd : "d".toList = ['d'] := by decide
    have h0 : (toString 0).toList = ['0'] := by decide
    have h1 : (toString 1).toList = ['1'] := by decide
    have h2 : (toString 2).toList = ['2'] := by decide
    have h3 : (toString 3).toList = ['3'] := by decide
    simp [hd, h0, h1, h2, h3] at h'

/-- Capability-valid and capability-lineage-valid names are disjoint. -/
theorem dcapV_ne_dcapLinV (d : DomainId) (s u : Slot) :
    dcapV d s ≠ dcapLinV d u := by
  fin_cases s <;> fin_cases u <;> decide +kernel +revert

/-- Capability-valid and lineage-cell-valid names are disjoint. -/
theorem dcapV_ne_dcellV (d : DomainId) (s : Slot) (l : LineageId) :
    dcapV d s ≠ dcellV d l := by
  intro h
  have h' := congrArg String.toList h
  have hcap : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hcell : "_cell".toList = ['_', 'c', 'e', 'l', 'l'] := by decide
  simp [dcapV, dcellV, toString_string, hcap, hcell] at h'

/-- Capability-valid names determine their slot within a domain. -/
theorem dcapV_inj_slot (d : DomainId) (s u : Slot) :
    dcapV d s = dcapV d u → s = u := by
  fin_cases s <;> fin_cases u <;> decide +kernel +revert

/-- Capability-kind names determine their slot within a domain. -/
theorem dcapKind_inj_slot (d : DomainId) (s u : Slot) :
    dcapKind d s = dcapKind d u → s = u := by
  fin_cases s <;> fin_cases u <;> decide +kernel +revert

/-- Capability-lineage-valid names determine their slot within a domain. -/
theorem dcapLinV_inj_slot (d : DomainId) (s u : Slot) :
    dcapLinV d s = dcapLinV d u → s = u := by
  fin_cases s <;> fin_cases u <;> decide +kernel +revert

/-- Capability-lineage names determine their slot within a domain. -/
theorem dcapLin_inj_slot (d : DomainId) (s u : Slot) :
    dcapLin d s = dcapLin d u → s = u := by
  fin_cases s <;> fin_cases u <;> decide +kernel +revert

/-- Lineage-cell-valid names determine their lineage index within a domain. -/
theorem dcellV_inj_lineage (d : DomainId) (l u : LineageId) :
    dcellV d l = dcellV d u → l = u := by
  fin_cases l <;> fin_cases u <;> decide +kernel +revert

/-- Lineage-cell-parent names determine their lineage index within a domain. -/
theorem dcellPar_inj_lineage (d : DomainId) (l u : LineageId) :
    dcellPar d l = dcellPar d u → l = u := by
  fin_cases l <;> fin_cases u <;> decide +kernel +revert

/-- Capability-kind and architectural-register names are disjoint. -/
theorem dcapKind_ne_dreg (d e : DomainId) (s : Slot) (r : RegId) :
    dcapKind d s ≠ dreg e r := by
  intro h
  have h' := congrArg String.toList h
  have hcap : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hreg : "_reg".toList = ['_', 'r', 'e', 'g'] := by decide
  have h0 : (toString 0).toList = ['0'] := by decide
  have h1 : (toString 1).toList = ['1'] := by decide
  have h2 : (toString 2).toList = ['2'] := by decide
  have h3 : (toString 3).toList = ['3'] := by decide
  fin_cases d <;> fin_cases e <;>
    simp [dcapKind, dreg, toString_string, hcap, hreg, h0, h1, h2, h3] at h'

theorem dreg_ne_domain (x y : DomainId) (hxy : x ≠ y) (r u : RegId) :
    dreg x r ≠ dreg y u := by
  simpa [dreg, toString_string, String.append_assoc] using
    domPrefix_ne x y hxy ("_reg" ++ toString r.val) ("_reg" ++ toString u.val)

theorem dpc_ne_domain (x y : DomainId) (hxy : x ≠ y) : dpc x ≠ dpc y := by
  simpa [dpc, toString_string, String.append_assoc] using
    domPrefix_ne x y hxy "_pc" "_pc"

/-- Capability-lineage-valid and lineage-cell-valid names are disjoint. -/
theorem dcapLinV_ne_dcellV (d : DomainId) (s : Slot) (l : LineageId) :
    dcapLinV d s ≠ dcellV d l := by
  intro h
  have h' := congrArg String.toList h
  have hcap : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hcell : "_cell".toList = ['_', 'c', 'e', 'l', 'l'] := by decide
  simp [dcapLinV, dcellV, toString_string, hcap, hcell] at h'

/-- Any domain-prefixed name is distinct from the global in-flight flag. -/
theorem dPrefix_ne_ifv (d : DomainId) (suffix : String) :
    "d" ++ (toString d.val ++ suffix) ≠ "if_v" := by
  intro h
  have h' := congrArg String.toList h
  have hd : "d".toList = ['d'] := by decide
  have hi : "if_v".toList = ['i', 'f', '_', 'v'] := by decide
  simp [hd, hi] at h'

theorem dcapLinV_ne_ifv (d : DomainId) (s : Slot) :
    dcapLinV d s ≠ "if_v" := by
  simpa [dcapLinV, toString_string, String.append_assoc] using
    dPrefix_ne_ifv d ("_cap" ++ (toString s.val ++ "_lin_v"))

theorem dcellV_ne_ifv (d : DomainId) (l : LineageId) :
    dcellV d l ≠ "if_v" := by
  simpa [dcellV, toString_string, String.append_assoc] using
    dPrefix_ne_ifv d ("_cell" ++ (toString l.val ++ "_v"))

/-- A domain capability-valid name is not the global in-flight flag. -/
theorem dcapV_ne_ifv (d : DomainId) (s : Slot) : dcapV d s ≠ "if_v" := by
  intro h
  have h' := congrArg String.toList h
  have hd : "d".toList = ['d'] := by decide
  have hi : "if_v".toList = ['i', 'f', '_', 'v'] := by decide
  simp [dcapV, toString_string, hd, hi] at h'

/-- A dynamic architectural-register write has a fixed seven-name write set. -/
theorem writeReg_writes (d : DomainId) (r : Loom.Hw.Expr 3)
    (v : Loom.Hw.Expr 32) :
    (writeReg d r v).regWrites =
      [(dreg d 1, 32), (dreg d 2, 32), (dreg d 3, 32),
       (dreg d 4, 32), (dreg d 5, 32), (dreg d 6, 32),
       (dreg d 7, 32)] := by
  rfl

end Machines.Lnp64u.Theorems.RMC
