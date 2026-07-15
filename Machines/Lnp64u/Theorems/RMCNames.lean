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

/-- Distinct suffixes remain distinct after adding encoded domain prefixes. -/
theorem domSuffix_ne (x y : DomainId) (a b : String) (hab : a ≠ b) :
    "d" ++ (toString x.val ++ a) ≠ "d" ++ (toString y.val ++ b) := by
  by_cases hxy : x = y
  · subst y
    intro h
    apply hab
    apply String.toList_injective
    have h' := congrArg String.toList h
    simpa using h'
  · exact domPrefix_ne x y hxy a b

private theorem capSuffix_ne_rgnSuffix (a b : String) :
    "_cap" ++ a ≠ "_rgn" ++ b := by
  intro h
  have h' := congrArg String.toList h
  have hc : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hr : "_rgn".toList = ['_', 'r', 'g', 'n'] := by decide
  simp [hc, hr] at h'

private theorem capSuffix_ne_srvSuffix (a b : String) :
    "_cap" ++ a ≠ "_srv" ++ b := by
  intro h
  have h' := congrArg String.toList h
  have hc : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hs : "_srv".toList = ['_', 's', 'r', 'v'] := by decide
  simp [hc, hs] at h'

private theorem cellSuffix_ne_rgnSuffix (a b : String) :
    "_cell" ++ a ≠ "_rgn" ++ b := by
  intro h
  have h' := congrArg String.toList h
  have hc : "_cell".toList = ['_', 'c', 'e', 'l', 'l'] := by decide
  have hr : "_rgn".toList = ['_', 'r', 'g', 'n'] := by decide
  simp [hc, hr] at h'

private theorem cellSuffix_ne_srvSuffix (a b : String) :
    "_cell" ++ a ≠ "_srv" ++ b := by
  intro h
  have h' := congrArg String.toList h
  have hc : "_cell".toList = ['_', 'c', 'e', 'l', 'l'] := by decide
  have hs : "_srv".toList = ['_', 's', 'r', 'v'] := by decide
  simp [hc, hs] at h'

private theorem capSuffix_ne_genSuffix (a b : String) :
    "_cap" ++ a ≠ "_gen" ++ b := by
  intro h
  have h' := congrArg String.toList h
  have hc : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hg : "_gen".toList = ['_', 'g', 'e', 'n'] := by decide
  simp [hc, hg] at h'

private theorem cellSuffix_ne_genSuffix (a b : String) :
    "_cell" ++ a ≠ "_gen" ++ b := by
  intro h
  have h' := congrArg String.toList h
  have hc : "_cell".toList = ['_', 'c', 'e', 'l', 'l'] := by decide
  have hg : "_gen".toList = ['_', 'g', 'e', 'n'] := by decide
  simp [hc, hg] at h'

private theorem capSuffix_ne_cause (a : String) : "_cap" ++ a ≠ "_cause" := by
  intro h
  have h' := congrArg String.toList h
  have hcap : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hcause : "_cause".toList = ['_', 'c', 'a', 'u', 's', 'e'] := by decide
  simp [hcap, hcause] at h'

private theorem capSuffix_ne_budget (a : String) : "_cap" ++ a ≠ "_budget" := by
  intro h
  have h' := congrArg String.toList h
  have hcap : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hbudget : "_budget".toList = ['_', 'b', 'u', 'd', 'g', 'e', 't'] := by decide
  simp [hcap, hbudget] at h'

private theorem capSuffix_ne_maxdon (a : String) : "_cap" ++ a ≠ "_maxdon" := by
  intro h
  have h' := congrArg String.toList h
  have hcap : "_cap".toList = ['_', 'c', 'a', 'p'] := by decide
  have hmax : "_maxdon".toList = ['_', 'm', 'a', 'x', 'd', 'o', 'n'] := by decide
  simp [hcap, hmax] at h'

theorem dcapV_ne_drgnV (d x : DomainId) (s : Slot) (r : RegionId) :
    dcapV d s ≠ drgnV x r := by
  simpa [dcapV, drgnV, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cap" ++ (toString s.val ++ "_v"))
      ("_rgn" ++ (toString r.val ++ "_v")) (capSuffix_ne_rgnSuffix _ _)

theorem dcapV_ne_dsrvV (d x : DomainId) (s : Slot) : dcapV d s ≠ dsrvV x := by
  simpa [dcapV, dsrvV, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cap" ++ (toString s.val ++ "_v")) ("_srv" ++ "_v")
      (capSuffix_ne_srvSuffix _ _)

theorem dcapLinV_ne_drgnV (d x : DomainId) (s : Slot) (r : RegionId) :
    dcapLinV d s ≠ drgnV x r := by
  simpa [dcapLinV, drgnV, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cap" ++ (toString s.val ++ "_lin_v"))
      ("_rgn" ++ (toString r.val ++ "_v")) (capSuffix_ne_rgnSuffix _ _)

theorem dcapLinV_ne_dsrvV (d x : DomainId) (s : Slot) :
    dcapLinV d s ≠ dsrvV x := by
  simpa [dcapLinV, dsrvV, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cap" ++ (toString s.val ++ "_lin_v")) ("_srv" ++ "_v")
      (capSuffix_ne_srvSuffix _ _)

theorem dcellV_ne_drgnV (d x : DomainId) (l : LineageId) (r : RegionId) :
    dcellV d l ≠ drgnV x r := by
  simpa [dcellV, drgnV, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cell" ++ (toString l.val ++ "_v"))
      ("_rgn" ++ (toString r.val ++ "_v")) (cellSuffix_ne_rgnSuffix _ _)

theorem dcellV_ne_dsrvV (d x : DomainId) (l : LineageId) :
    dcellV d l ≠ dsrvV x := by
  simpa [dcellV, dsrvV, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cell" ++ (toString l.val ++ "_v")) ("_srv" ++ "_v")
      (cellSuffix_ne_srvSuffix _ _)

theorem dcapV_ne_dgen (d x : DomainId) (s u : Slot) : dcapV d s ≠ dgen x u := by
  simpa [dcapV, dgen, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cap" ++ (toString s.val ++ "_v"))
      ("_gen" ++ toString u.val) (capSuffix_ne_genSuffix _ _)

theorem dcellV_ne_dgen (d x : DomainId) (l : LineageId) (s : Slot) :
    dcellV d l ≠ dgen x s := by
  simpa [dcellV, dgen, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cell" ++ (toString l.val ++ "_v"))
      ("_gen" ++ toString s.val) (cellSuffix_ne_genSuffix _ _)

theorem dcapKind_ne_dcause (d x : DomainId) (s : Slot) :
    dcapKind d s ≠ dcause x := by
  simpa [dcapKind, dcause, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cap" ++ (toString s.val ++ "_kind")) "_cause"
      (capSuffix_ne_cause _)

theorem dcapKind_ne_dbudget (d x : DomainId) (s : Slot) :
    dcapKind d s ≠ dbudget x := by
  simpa [dcapKind, dbudget, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cap" ++ (toString s.val ++ "_kind")) "_budget"
      (capSuffix_ne_budget _)

theorem dcapKind_ne_dmaxdon (d x : DomainId) (s : Slot) :
    dcapKind d s ≠ dmaxdon x := by
  simpa [dcapKind, dmaxdon, toString_string, String.append_assoc] using
    domSuffix_ne d x ("_cap" ++ (toString s.val ++ "_kind")) "_maxdon"
      (capSuffix_ne_maxdon _)

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

theorem dgen_inj_slot (d : DomainId) (s u : Slot) :
    dgen d s = dgen d u → s = u := by
  fin_cases s <;> fin_cases u <;> decide +kernel +revert

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
