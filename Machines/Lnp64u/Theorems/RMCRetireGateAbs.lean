-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGate

/-!
# R-MC retirement: gate-transfer abstraction

Whole-state abstraction lemmas for the capability transfer shared by
`gate_call` and `gate_return`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 3200000
set_option maxRecDepth 200000

private theorem dcellPar_ne_dcapV (c : DomainId) (l : LineageId)
    (s : Slot) : Hw.dcellPar c l ≠ Hw.dcapV c s := by
  fin_cases c <;> decide +kernel +revert

private theorem dcellPar_ne_dcapKind (c : DomainId) (l : LineageId)
    (s : Slot) : Hw.dcellPar c l ≠ Hw.dcapKind c s := by
  fin_cases c <;> decide +kernel +revert

private theorem dcellPar_ne_dcapLinV (c : DomainId) (l : LineageId)
    (s : Slot) : Hw.dcellPar c l ≠ Hw.dcapLinV c s := by
  fin_cases c <;> decide +kernel +revert

private theorem dcellPar_ne_dcapLin (c : DomainId) (l : LineageId)
    (s : Slot) : Hw.dcellPar c l ≠ Hw.dcapLin c s := by
  fin_cases c <;> decide +kernel +revert

/-! ## Selected installation abstraction -/

/-- Abstract recipient-side update performed by a transfer installation.
The optional pair carries the newly allocated lineage cell and its parent. -/
def installTransferred (τ : MachineState) (c : DomainId) (NS : Slot)
    (kind : CapKind) (moved : Option (LineageId × CapRef)) : MachineState :=
  τ.setDom c fun ds =>
    { ds with
      caps := Loom.Fun.update ds.caps NS
        (some { kind := kind, lineage := moved.map Prod.fst })
      lineage := match moved with
        | some (l, parent) =>
            Loom.Fun.update ds.lineage l (some { parent := parent })
        | none => ds.lineage }

/-- The validity face of a selected transfer installation. -/
private theorem installA_selected_capV (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (s : Slot) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapV c s) 1 =
      if s = NS then 1#1 else acc.regs (Hw.dcapV c s) 1 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1 <;>
    simp only [hl, if_true, if_false, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
  all_goals
    by_cases hs : s = NS
    · subst s
      simp [Expr.eval, dcapV_ne_dcellV, dcapV_ne_dcapLinV]
    · have hname : Hw.dcapV c s ≠ Hw.dcapV c NS := fun h =>
        hs (dcapV_inj_slot c s NS h)
      simp [hs, dcapV_ne_dcellV, dcapV_ne_dcapLinV, hname]

/-- The kind face of a selected transfer installation. -/
private theorem installA_selected_capKind (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (s : Slot) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapKind c s) 32 =
      if s = NS then kindE.eval σ else acc.regs (Hw.dcapKind c s) 32 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1 <;>
    simp only [hl, if_true, if_false, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
  all_goals
    by_cases hs : s = NS
    · subst s
      simp
    · have hname : Hw.dcapKind c s ≠ Hw.dcapKind c NS := fun h =>
        hs (dcapKind_inj_slot c s NS h)
      simp [hs, hname]

/-- The lineage-valid face of a selected transfer installation. -/
private theorem installA_selected_capLinV (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (s : Slot) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapLinV c s) 1 =
      if s = NS then linVE.eval σ else acc.regs (Hw.dcapLinV c s) 1 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1 <;>
    simp only [hl, if_true, if_false, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
  all_goals
    by_cases hs : s = NS
    · subst s
      simp [dcapLinV_ne_dcellV]
    · have hcap : Hw.dcapLinV c s ≠ Hw.dcapV c NS := fun h =>
        dcapV_ne_dcapLinV c NS s h.symm
      have hname : Hw.dcapLinV c s ≠ Hw.dcapLinV c NS := fun h =>
        hs (dcapLinV_inj_slot c s NS h)
      simp [hs, dcapLinV_ne_dcellV, hcap, hname]

/-- The lineage-index face of a selected transfer installation. -/
private theorem installA_selected_capLin (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (s : Slot) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcapLin c s) 4 =
      if s = NS then nlE.eval σ else acc.regs (Hw.dcapLin c s) 4 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1 <;>
    simp only [hl, if_true, if_false, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
  all_goals
    by_cases hs : s = NS
    · subst s
      simp
    · have hname : Hw.dcapLin c s ≠ Hw.dcapLin c NS := fun h =>
        hs (dcapLin_inj_slot c s NS h)
      simp [hs, hname]

/-- The cell-valid face of a selected transfer installation. -/
private theorem installA_selected_cellV (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (l : LineageId) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcellV c l) 1 =
      if linVE.eval σ = 1#1 ∧ l = finOfBv (by decide) (nlE.eval σ) then
        1#1 else acc.regs (Hw.dcellV c l) 1 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1
  · simp only [hl, if_true, true_and, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
    by_cases heq : l = finOfBv (by decide) (nlE.eval σ)
    · subst l
      simp [Expr.eval]
    · have hcap : Hw.dcellV c l ≠ Hw.dcapV c NS := fun h =>
        dcapV_ne_dcellV c NS l h.symm
      have hlin : Hw.dcellV c l ≠ Hw.dcapLinV c NS := fun h =>
        dcapLinV_ne_dcellV c NS l h.symm
      have hcell : Hw.dcellV c l ≠
          Hw.dcellV c (finOfBv (by decide) (nlE.eval σ)) := fun h =>
        heq (dcellV_inj_lineage c l _ h)
      simp [heq, hcap, hlin, hcell]
  · have hcap : Hw.dcellV c l ≠ Hw.dcapV c NS := fun h =>
      dcapV_ne_dcellV c NS l h.symm
    have hlin : Hw.dcellV c l ≠ Hw.dcapLinV c NS := fun h =>
      dcapLinV_ne_dcellV c NS l h.symm
    simp only [hl, if_false]
    apply frame
    simp [Hw.seqAll, Act.regWrites, hcap, hlin]

/-- The cell-parent face of a selected transfer installation. -/
private theorem installA_selected_cellPar (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) (l : LineageId) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
        (Hw.dcellPar c l) 14 =
      if linVE.eval σ = 1#1 ∧ l = finOfBv (by decide) (nlE.eval σ) then
        parE.eval σ else acc.regs (Hw.dcellPar c l) 14 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1
  · simp only [hl, if_true, true_and, Act.run, Hw.seqAll, List.foldr,
      RegEnv.set]
    by_cases heq : l = finOfBv (by decide) (nlE.eval σ)
    · subst l
      simp
    · have hcell : Hw.dcellPar c l ≠
          Hw.dcellPar c (finOfBv (by decide) (nlE.eval σ)) := fun h =>
        heq (dcellPar_inj_lineage c l _ h)
      simp [heq, dcellPar_ne_dcapV, dcellPar_ne_dcapKind,
        dcellPar_ne_dcapLinV, dcellPar_ne_dcapLin, hcell]
  · simp only [hl, if_false]
    apply frame
    simp [Hw.seqAll, Act.regWrites, dcellPar_ne_dcapV,
      dcellPar_ne_dcapKind, dcellPar_ne_dcapLinV, dcellPar_ne_dcapLin]


/-- A selected installation frames any register key outside its six concrete
table writes. -/
theorem installA_selected_frame (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (q : String × Nat)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hv : q ≠ (Hw.dcapV c NS, 1))
    (hk : q ≠ (Hw.dcapKind c NS, 32))
    (hlv : q ≠ (Hw.dcapLinV c NS, 1))
    (hli : q ≠ (Hw.dcapLin c NS, 4))
    (hcv : q ≠ (Hw.dcellV c (finOfBv (by decide) (nlE.eval σ)), 1))
    (hcp : q ≠ (Hw.dcellPar c (finOfBv (by decide) (nlE.eval σ)), 14)) :
    ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs q.1 q.2 =
      acc.regs q.1 q.2 := by
  rw [installA_run_selected_any σ acc c nsE kindE linVE nlE parE NS hns]
  dsimp only
  by_cases hl : linVE.eval σ = 1#1
  · simp only [hl, if_true]
    apply frame
    simp [Hw.seqAll, Act.regWrites, hv, hk, hlv, hli, hcv, hcp]
  · simp only [hl, if_false]
    apply frame
    simp [Hw.seqAll, Act.regWrites, hv, hk, hlv, hli]

private theorem installA_selected_quiet (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) :
    ∀ q ∈ domQuietNamesCap c,
      ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs q.1 q.2 =
        acc.regs q.1 q.2 := by
  intro q hq
  let NL : LineageId := finOfBv (by decide) (nlE.eval σ)
  have htV : ((Hw.dcapV c NS : String), 1) ∉ domQuietNamesCap c := by
    simp [domQuietNamesCap, dcapV_ne_drgnV, dcapV_ne_dsrvV]
  have htK : ((Hw.dcapKind c NS : String), 32) ∉ domQuietNamesCap c := by
    simp [domQuietNamesCap, dcapKind_ne_dcause, dcapKind_ne_dbudget,
      dcapKind_ne_dmaxdon]
  have htLV : ((Hw.dcapLinV c NS : String), 1) ∉ domQuietNamesCap c := by
    simp [domQuietNamesCap, dcapLinV_ne_drgnV, dcapLinV_ne_dsrvV]
  have htL : ((Hw.dcapLin c NS : String), 4) ∉ domQuietNamesCap c := by
    simp [domQuietNamesCap]
  have hcV : ((Hw.dcellV c NL : String), 1) ∉ domQuietNamesCap c := by
    simp [domQuietNamesCap, dcellV_ne_drgnV, dcellV_ne_dsrvV]
  have hcP : ((Hw.dcellPar c NL : String), 14) ∉ domQuietNamesCap c := by
    simp [domQuietNamesCap]
  apply installA_selected_frame σ acc c nsE kindE linVE nlE parE NS q hns
  all_goals
    intro heq
    subst q
    first | exact htV hq | exact htK hq | exact htLV hq |
      exact htL hq | exact hcV hq | exact hcP hq

/-- Capability-table abstraction of a selected transfer installation. -/
theorem absDom_installA_selected_caps (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind) :
    (Hw.absDom ((Hw.installA c nsE kindE linVE nlE parE).run σ acc) c).caps =
      Loom.Fun.update (Hw.absDom acc c).caps NS
        (some { kind := kind
                lineage := if linVE.eval σ = 1#1 then
                  some (finOfBv (by decide) (nlE.eval σ)) else none }) := by
  funext s
  show (if ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
      (Hw.dcapV c s) 1 = 1#1 then
        some (CapEntry.mk (Hw.decKind
          (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
            (Hw.dcapKind c s) 32))
          (if ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
            (Hw.dcapLinV c s) 1 = 1#1 then
              some (finOfBv (by decide)
                (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
                  (Hw.dcapLin c s) 4))
            else none))
      else none) = _
  by_cases hs : s = NS
  · subst s
    rw [Loom.Fun.update_same,
      installA_selected_capV σ acc c nsE kindE linVE nlE parE NS hns,
      if_pos rfl,
      installA_selected_capKind σ acc c nsE kindE linVE nlE parE NS hns,
      if_pos rfl,
      installA_selected_capLinV σ acc c nsE kindE linVE nlE parE NS hns,
      if_pos rfl,
      installA_selected_capLin σ acc c nsE kindE linVE nlE parE NS hns,
      if_pos rfl, hkind, decKind_encKind]
    simp
  · rw [Loom.Fun.update_ne _ _ _ _ hs,
      installA_selected_capV σ acc c nsE kindE linVE nlE parE NS hns,
      if_neg hs,
      installA_selected_capKind σ acc c nsE kindE linVE nlE parE NS hns,
      if_neg hs,
      installA_selected_capLinV σ acc c nsE kindE linVE nlE parE NS hns,
      if_neg hs,
      installA_selected_capLin σ acc c nsE kindE linVE nlE parE NS hns,
      if_neg hs]
    rfl

/-- Lineage-table abstraction of a selected transfer installation. -/
theorem absDom_installA_selected_lineage (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) :
    (Hw.absDom ((Hw.installA c nsE kindE linVE nlE parE).run σ acc) c).lineage =
      if linVE.eval σ = 1#1 then
        Loom.Fun.update (Hw.absDom acc c).lineage
          (finOfBv (by decide) (nlE.eval σ))
          (some { parent := Hw.decRef (parE.eval σ) })
      else (Hw.absDom acc c).lineage := by
  funext l
  show (if ((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
      (Hw.dcellV c l) 1 = 1#1 then
        some (LineageCell.mk (Hw.decRef
          (((Hw.installA c nsE kindE linVE nlE parE).run σ acc).regs
            (Hw.dcellPar c l) 14)))
      else none) = _
  rw [installA_selected_cellV σ acc c nsE kindE linVE nlE parE NS hns,
    installA_selected_cellPar σ acc c nsE kindE linVE nlE parE NS hns]
  by_cases hl : linVE.eval σ = 1#1
  · rw [if_pos hl]
    by_cases heq : l = finOfBv (by decide) (nlE.eval σ)
    · subst l
      simp [hl, Hw.absDom]
    · simp [hl, heq, Hw.absDom]
  · simp [hl, Hw.absDom]

/-- Whole-domain abstraction of a selected transfer installation. This is
the table update used by both successful gate-transfer paths. -/
theorem absDom_installA_selected (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind) :
    Hw.absDom ((Hw.installA c nsE kindE linVE nlE parE).run σ acc) c =
      { Hw.absDom acc c with
        caps := Loom.Fun.update (Hw.absDom acc c).caps NS
          (some { kind := kind
                  lineage := if linVE.eval σ = 1#1 then
                    some (finOfBv (by decide) (nlE.eval σ)) else none })
        lineage := if linVE.eval σ = 1#1 then
          Loom.Fun.update (Hw.absDom acc c).lineage
            (finOfBv (by decide) (nlE.eval σ))
            (some { parent := Hw.decRef (parE.eval σ) })
        else (Hw.absDom acc c).lineage } := by
  rw [absDom_regpccap c
    (installA_selected_quiet σ acc c nsE kindE linVE nlE parE NS hns)]
  apply domainState_ext'
  · funext r
    apply installA_selected_frame σ acc c nsE kindE linVE nlE parE NS
      (Hw.dreg c r, 32) hns
    · simp
    · intro h
      exact dcapKind_ne_dreg c c NS r (congrArg Prod.fst h).symm
    all_goals simp
  · apply installA_selected_frame σ acc c nsE kindE linVE nlE parE NS
      (Hw.dpc c, 12) hns <;> simp
  · exact absDom_installA_selected_caps σ acc c nsE kindE linVE nlE parE
      NS kind hns hkind
  · rfl
  · exact absDom_installA_selected_lineage σ acc c nsE kindE linVE nlE parE
      NS hns
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem domReadNames_prefix (x : DomainId) (q : String × Nat)
    (hq : q ∈ domReadNames x) :
    ∃ suffix, q.1 = "d" ++ (toString x.val ++ suffix) := by
  rcases q with ⟨rn, w⟩
  simp [domReadNames, Hw.dreg, Hw.dpc, Hw.dcapV, Hw.dcapKind,
    Hw.dcapLinV, Hw.dcapLin, Hw.dgen, Hw.dcellV, Hw.dcellPar, Hw.drgnV,
    Hw.drgn, Hw.drun, Hw.drunG, Hw.dsrvV, Hw.dsrv, Hw.dcause, Hw.dbudget,
    Hw.dmaxdon, toString_string, String.append_assoc] at hq ⊢
  aesop

/-- A selected installation changes no non-recipient domain. -/
theorem absDom_installA_selected_other (σ acc : Loom.Hw.St)
    (c x : DomainId) (hxc : x ≠ c)
    (nsE : Expr 4) (kindE : Expr 32) (linVE : Expr 1)
    (nlE : Expr 4) (parE : Expr 14) (NS : Slot)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val) :
    Hw.absDom ((Hw.installA c nsE kindE linVE nlE parE).run σ acc) x =
      Hw.absDom acc x := by
  apply absDom_congr
  intro q hq
  obtain ⟨suffix, hsuffix⟩ := domReadNames_prefix x q hq
  rcases q with ⟨rn, w⟩
  simp only at hsuffix
  subst rn
  apply installA_selected_frame σ acc c nsE kindE linVE nlE parE NS
    ("d" ++ (toString x.val ++ suffix), w) hns
  all_goals
    intro heq
    have hn := congrArg Prod.fst heq
    simp [Hw.dcapV, Hw.dcapKind, Hw.dcapLinV, Hw.dcapLin, Hw.dcellV,
      Hw.dcellPar, toString_string, String.append_assoc,
      domPrefix_ne x c hxc] at hn

/-- All-domain form of the selected-installation abstraction. -/
theorem abs_installA_selected_doms (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind) :
    (Hw.abs ((Hw.installA c nsE kindE linVE nlE parE).run σ acc)).doms =
      Loom.Fun.update (Hw.abs acc).doms c
        { Hw.absDom acc c with
          caps := Loom.Fun.update (Hw.absDom acc c).caps NS
            (some { kind := kind
                    lineage := if linVE.eval σ = 1#1 then
                      some (finOfBv (by decide) (nlE.eval σ)) else none })
          lineage := if linVE.eval σ = 1#1 then
            Loom.Fun.update (Hw.absDom acc c).lineage
              (finOfBv (by decide) (nlE.eval σ))
              (some { parent := Hw.decRef (parE.eval σ) })
          else (Hw.absDom acc c).lineage } := by
  funext x
  by_cases hxc : x = c
  · subst x
    rw [Loom.Fun.update_same]
    exact absDom_installA_selected σ acc c nsE kindE linVE nlE parE NS
      kind hns hkind
  · rw [Loom.Fun.update_ne _ _ _ _ hxc]
    exact absDom_installA_selected_other σ acc c x hxc nsE kindE linVE nlE
      parE NS hns

/-- Machine-state spelling of the selected-installation bridge. -/
theorem abs_installA_selected (σ acc : Loom.Hw.St)
    (c : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind) :
    (Hw.abs ((Hw.installA c nsE kindE linVE nlE parE).run σ acc)).doms =
      (installTransferred (Hw.abs acc) c NS kind
        (if linVE.eval σ = 1#1 then
          some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
        else none)).doms := by
  rw [abs_installA_selected_doms σ acc c nsE kindE linVE nlE parE NS kind
    hns hkind]
  unfold installTransferred MachineState.setDom
  dsimp only
  congr 1
  by_cases hl : linVE.eval σ = 1#1 <;> simp [hl, Hw.abs]

/-! ## Installation followed by reparenting -/

/-- Reparenting after a selected installation.  The fresh lineage cell is
the sole exception to the usual pre-cycle/accumulator agreement premise:
it was free in the sampled state and its already-adjusted parent is not the
old reference, so neither the hardware nor abstract reparent pass changes it. -/
theorem absDom_reparent_installA_selected (σ acc : Loom.Hw.St)
    (T : DomainId) (nsE : Expr 4) (kindE : Expr 32)
    (linVE : Expr 1) (nlE : Expr 4) (parE oldE newE : Expr 14)
    (NS : Slot) (kind : CapKind)
    (hns : nsE.eval σ = BitVec.ofNat 4 NS.val)
    (hkind : kindE.eval σ = Hw.encKind kind)
    (hV : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellV c l) 1 = σ.regs (Hw.dcellV c l) 1)
    (hP : ∀ c : DomainId, ∀ l : LineageId,
      acc.regs (Hw.dcellPar c l) 14 = σ.regs (Hw.dcellPar c l) 14)
    (hfree : linVE.eval σ = 1#1 →
      σ.regs (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 ≠ 1#1)
    (hparent : linVE.eval σ = 1#1 →
      Hw.decRef (parE.eval σ) ≠ Hw.decRef (oldE.eval σ))
    (c : DomainId) :
    Hw.absDom ((Hw.reparentA oldE newE).run σ
        ((Hw.installA T nsE kindE linVE nlE parE).run σ acc)) c =
      ((installTransferred (Hw.abs acc) T NS kind
        (if linVE.eval σ = 1#1 then
          some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
        else none)).reparent (Hw.decRef (oldE.eval σ))
          (Hw.decRef (newE.eval σ))).doms c := by
  let inst := (Hw.installA T nsE kindE linVE nlE parE).run σ acc
  let τi := installTransferred (Hw.abs acc) T NS kind
    (if linVE.eval σ = 1#1 then
      some (finOfBv (by decide) (nlE.eval σ), Hw.decRef (parE.eval σ))
    else none)
  have hi : (Hw.abs inst).doms = τi.doms := by
    exact abs_installA_selected σ acc T nsE kindE linVE nlE parE NS kind
      hns hkind
  have hr : ((Hw.abs inst).reparent (Hw.decRef (oldE.eval σ))
      (Hw.decRef (newE.eval σ))).doms =
      (τi.reparent (Hw.decRef (oldE.eval σ))
        (Hw.decRef (newE.eval σ))).doms := by
    unfold MachineState.reparent
    dsimp only
    rw [hi]
  change Hw.absDom ((Hw.reparentA oldE newE).run σ inst) c = _
  rw [← congrFun hr c]
  unfold MachineState.reparent
  dsimp only
  apply domainState_ext
  · funext r
    exact reparentA_frame_width σ inst oldE newE (Hw.dreg c r) 32
      (by decide)
  · exact reparentA_frame_width σ inst oldE newE (Hw.dpc c) 12 (by decide)
  · funext s
    exact abs_reparentA_caps σ inst oldE newE c s
  · funext s
    exact abs_reparentA_slotGen σ inst oldE newE c s
  · funext l
    by_cases hl : linVE.eval σ = 1#1
    · by_cases hexc : c = T ∧
          l = finOfBv (by decide) (nlE.eval σ)
      · obtain ⟨hc, hl'⟩ := hexc
        subst c
        subst l
        dsimp only
        change (if ((Hw.reparentA oldE newE).run σ inst).regs
            (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 = 1#1 then
          some (LineageCell.mk (Hw.decRef
            (((Hw.reparentA oldE newE).run σ inst).regs
              (Hw.dcellPar T (finOfBv (by decide) (nlE.eval σ))) 14)))
          else none) =
          match (if inst.regs
              (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 = 1#1 then
            some (LineageCell.mk (Hw.decRef (inst.regs
              (Hw.dcellPar T (finOfBv (by decide) (nlE.eval σ))) 14)))
          else none) with
          | some cell => some (if cell.parent = Hw.decRef (oldE.eval σ) then
              LineageCell.mk (Hw.decRef (newE.eval σ)) else cell)
          | none => none
        rw [reparentA_frame_width σ inst oldE newE
          (Hw.dcellV T (finOfBv (by decide) (nlE.eval σ))) 1 (by decide),
          installA_selected_cellV σ acc T nsE kindE linVE nlE parE NS hns,
          reparentA_cellPar σ inst oldE newE T
            (finOfBv (by decide) (nlE.eval σ)),
          installA_selected_cellPar σ acc T nsE kindE linVE nlE parE NS hns]
        have hfree0 := bv1_ne_one.mp (hfree hl)
        simp [Expr.eval, hl, hfree0, hparent hl]
      · have hVi : inst.regs (Hw.dcellV c l) 1 =
            σ.regs (Hw.dcellV c l) 1 := by
          by_cases hcT : c = T
          · subst c
            have hne : l ≠ finOfBv (by decide) (nlE.eval σ) := by
              intro h
              exact hexc ⟨rfl, h⟩
            simpa [inst, hl, hne, hV T l] using
              (installA_selected_cellV σ acc T nsE kindE linVE nlE parE NS
                hns l)
          · have hreg : inst.regs (Hw.dcellV c l) 1 =
                acc.regs (Hw.dcellV c l) 1 := by
              apply installA_selected_frame σ acc T nsE kindE linVE nlE
                parE NS (Hw.dcellV c l, 1) hns
              · intro h
                exact dcapV_ne_dcellV_any T c NS l
                  (congrArg Prod.fst h).symm
              · simp
              · intro h
                exact dcapLinV_ne_dcellV_any T c NS l
                  (congrArg Prod.fst h).symm
              · simp
              · intro h
                exact hcT (dcellV_inj_pair c T l _
                  (congrArg Prod.fst h)).1
              · simp
            exact hreg.trans (hV c l)
        have hPi : inst.regs (Hw.dcellPar c l) 14 =
            σ.regs (Hw.dcellPar c l) 14 := by
          by_cases hcT : c = T
          · subst c
            have hne : l ≠ finOfBv (by decide) (nlE.eval σ) := by
              intro h
              exact hexc ⟨rfl, h⟩
            simpa [inst, hl, hne, hP T l] using
              (installA_selected_cellPar σ acc T nsE kindE linVE nlE parE NS
                hns l)
          · have hreg : inst.regs (Hw.dcellPar c l) 14 =
                acc.regs (Hw.dcellPar c l) 14 := by
              apply installA_selected_frame σ acc T nsE kindE linVE nlE
                parE NS (Hw.dcellPar c l, 14) hns
              · simp
              · simp
              · simp
              · simp
              · simp
              · intro h
                exact hcT (dcellPar_inj_pair c T l _
                  (congrArg Prod.fst h)).1
            exact hreg.trans (hP c l)
        exact abs_reparentA_lineage σ inst oldE newE c l hVi hPi
    · have hVi : inst.regs (Hw.dcellV c l) 1 =
          σ.regs (Hw.dcellV c l) 1 := by
        by_cases hcT : c = T
        · subst c
          simpa [inst, hl] using
            (installA_selected_cellV σ acc T nsE kindE linVE nlE parE NS
              hns l).trans (by simp [hl, hV T l])
        · have hreg : inst.regs (Hw.dcellV c l) 1 =
              acc.regs (Hw.dcellV c l) 1 := by
            apply installA_selected_frame σ acc T nsE kindE linVE nlE parE
              NS (Hw.dcellV c l, 1) hns
            · intro h
              exact dcapV_ne_dcellV_any T c NS l (congrArg Prod.fst h).symm
            · simp
            · intro h
              exact dcapLinV_ne_dcellV_any T c NS l
                (congrArg Prod.fst h).symm
            · simp
            · intro h
              exact hcT (dcellV_inj_pair c T l _ (congrArg Prod.fst h)).1
            · simp
          exact hreg.trans (hV c l)
      have hPi : inst.regs (Hw.dcellPar c l) 14 =
          σ.regs (Hw.dcellPar c l) 14 := by
        by_cases hcT : c = T
        · subst c
          simpa [inst, hl] using
            (installA_selected_cellPar σ acc T nsE kindE linVE nlE parE NS
              hns l).trans (by simp [hl, hP T l])
        · have hreg : inst.regs (Hw.dcellPar c l) 14 =
              acc.regs (Hw.dcellPar c l) 14 := by
            apply installA_selected_frame σ acc T nsE kindE linVE nlE parE
              NS (Hw.dcellPar c l, 14) hns
            · simp
            · simp
            · simp
            · simp
            · simp
            · intro h
              exact hcT (dcellPar_inj_pair c T l _
                (congrArg Prod.fst h)).1
          exact hreg.trans (hP c l)
      exact abs_reparentA_lineage σ inst oldE newE c l hVi hPi
  · funext r
    change (if ((Hw.reparentA oldE newE).run σ inst).regs
        (Hw.drgnV c r) 1 = 1#1 then
      some (Hw.decRegion (((Hw.reparentA oldE newE).run σ inst).regs
        (Hw.drgn c r) 42)) else none) = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.drgnV c r) 1
      (by decide), reparentA_frame_width σ inst oldE newE (Hw.drgn c r) 42
      (by decide)]
    rfl
  ·
    change Hw.decRun
      (((Hw.reparentA oldE newE).run σ inst).regs (Hw.drun c) 2)
      (((Hw.reparentA oldE newE).run σ inst).regs (Hw.drunG c) 2) = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.drun c) 2 (by decide),
      reparentA_frame_width σ inst oldE newE (Hw.drunG c) 2 (by decide)]
    rfl
  ·
    change (if ((Hw.reparentA oldE newE).run σ inst).regs
        (Hw.dsrvV c) 1 = 1#1 then
      some (finOfBv (by decide)
        (((Hw.reparentA oldE newE).run σ inst).regs (Hw.dsrv c) 2))
      else none) = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.dsrvV c) 1 (by decide),
      reparentA_frame_width σ inst oldE newE (Hw.dsrv c) 2 (by decide)]
    rfl
  · exact reparentA_frame_width σ inst oldE newE (Hw.dcause c) 32 (by decide)
  ·
    change (((Hw.reparentA oldE newE).run σ inst).regs
      (Hw.dbudget c) 32).toNat = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.dbudget c) 32 (by decide)]
    rfl
  ·
    change (((Hw.reparentA oldE newE).run σ inst).regs
      (Hw.dmaxdon c) 32).toNat = _
    rw [reparentA_frame_width σ inst oldE newE (Hw.dmaxdon c) 32 (by decide)]
    rfl

/-- Pre-adjusting the moved cell's parent is equivalent, on the domain map,
to letting the abstract reparent pass adjust it. This is the semantic reason
for the parent mux inside `Hw.transferA`. -/
theorem installTransferred_reparent_adjusted_doms (τ : MachineState)
    (T : DomainId) (NS : Slot) (kind : CapKind) (NL : LineageId)
    (parent oldRef newRef : CapRef) (hne : newRef ≠ oldRef) :
    ((installTransferred τ T NS kind
        (some (NL, if parent = oldRef then newRef else parent))).reparent
      oldRef newRef).doms =
    ((installTransferred τ T NS kind (some (NL, parent))).reparent
      oldRef newRef).doms := by
  by_cases hp : parent = oldRef
  · subst parent
    funext d
    by_cases hd : d = T
    · subst d
      apply domainState_ext'
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · funext l
        by_cases hl : l = NL
        · subst l
          simp [installTransferred, MachineState.reparent,
            MachineState.setDom, hne]
        · simp [installTransferred, MachineState.reparent,
            MachineState.setDom, hl]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
      · simp [installTransferred, MachineState.reparent,
          MachineState.setDom]
    · simp [installTransferred, MachineState.reparent, MachineState.setDom,
        hd]
  · simp [installTransferred, MachineState.reparent, MachineState.setDom,
      hp]

end Machines.Lnp64u.Theorems.RMC
