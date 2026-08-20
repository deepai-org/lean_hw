-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Emit.MicroVerilog.RoundTrip
import Loom.Emit.MicroVerilog.Semantics

/-!
# Behavioral meaning of `Module.Matches`

`Matches` records exactly the module information represented in emitted text.
With reset semantics restricted to each finite hardware address space, that
information determines both reset and cycle behavior completely.
-/

namespace Loom.Emit.MicroVerilog

private theorem St.eq_of_fields {a b : St} (hr : a.regs = b.regs)
    (hm : a.mems = b.mems) : a = b := by
  rcases a with ⟨ar, am⟩
  rcases b with ⟨br, bm⟩
  change ar = br at hr
  change am = bm at hm
  cases hr
  cases hm
  rfl

private theorem MemDef.Matches.cycleStep_eq {a b : MemDef}
    (h : a.Matches b) (σ : St) (μ : MemEnv) :
    a.wrPorts.foldl (fun state port => port.commit a.name σ state) μ =
      b.wrPorts.foldl (fun state port => port.commit b.name σ state) μ := by
  rcases a with ⟨an, aaw, adw, ai, ap⟩
  rcases b with ⟨bn, baw, bdw, bi, bp⟩
  simp at h ⊢
  rcases h with ⟨hn, haw, hdw, hp, _⟩
  cases hn
  cases haw
  cases hdw
  cases eq_of_heq hp
  rfl

private theorem memCycleFold_eq (σ : St) :
    ∀ {as bs : List MemDef}, List.Forall₂ MemDef.Matches as bs →
      ∀ μ,
      as.foldl
          (fun state mem => mem.wrPorts.foldl
            (fun state port => port.commit mem.name σ state) state) μ =
      bs.foldl
          (fun state mem => mem.wrPorts.foldl
            (fun state port => port.commit mem.name σ state) state) μ
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons head tail, μ => by
      simp only [List.foldl_cons]
      rw [head.cycleStep_eq σ μ]
      exact memCycleFold_eq σ tail _

private theorem MemDef.Matches.resetStep_eq {a b : MemDef}
    (h : a.Matches b) (μ : MemEnv) :
    (fun n address width =>
      if n = a.name ∧ width = a.dataWidth ∧ address < 2 ^ a.addrWidth then
        (a.init address).setWidth width
      else μ n address width) =
    (fun n address width =>
      if n = b.name ∧ width = b.dataWidth ∧ address < 2 ^ b.addrWidth then
        (b.init address).setWidth width
      else μ n address width) := by
  rcases a with ⟨an, aaw, adw, ai, ap⟩
  rcases b with ⟨bn, baw, bdw, bi, bp⟩
  simp at h ⊢
  rcases h with ⟨hn, haw, hdw, _, hi⟩
  cases hn
  cases haw
  cases hdw
  funext name address width
  by_cases hc : name = an ∧ width = adw ∧ address < 2 ^ aaw
  · rw [if_pos hc, if_pos hc]
    obtain ⟨_, rfl, ha⟩ := hc
    apply BitVec.eq_of_toNat_eq
    simpa using hi address ha
  · rw [if_neg hc, if_neg hc]

private theorem memResetFold_eq :
    ∀ {as bs : List MemDef}, List.Forall₂ MemDef.Matches as bs →
      ∀ μ,
      as.foldl (fun state mem => fun n address width =>
          if n = mem.name ∧ width = mem.dataWidth ∧
              address < 2 ^ mem.addrWidth then
            (mem.init address).setWidth width
          else state n address width) μ =
      bs.foldl (fun state mem => fun n address width =>
          if n = mem.name ∧ width = mem.dataWidth ∧
              address < 2 ^ mem.addrWidth then
            (mem.init address).setWidth width
          else state n address width) μ
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons head tail, μ => by
      simp only [List.foldl_cons]
      rw [head.resetStep_eq μ]
      exact memResetFold_eq tail _

/-- Structurally matching modules have exactly the same reset state. -/
theorem Module.Matches.reset_eq {a b : Module} (h : a.Matches b) :
    a.reset = b.reset := by
  rcases h with ⟨_, _, _, _, _, hregs, _, hmems, _⟩
  have hr : a.reset.regs = b.reset.regs := by
    simp only [Module.reset]
    rw [hregs]
  have hm : a.reset.mems = b.reset.mems := by
    simp only [Module.reset]
    exact memResetFold_eq hmems _
  exact St.eq_of_fields hr hm

/-- Structurally matching modules have exactly the same one-cycle transition
on every state. -/
theorem Module.Matches.cycle_eq {a b : Module} (h : a.Matches b) (σ : St) :
    a.cycle σ = b.cycle σ := by
  rcases h with ⟨_, _, _, _, _, hregs, _, hmems, _⟩
  have hr : (a.cycle σ).regs = (b.cycle σ).regs := by
    simp only [Module.cycle]
    rw [hregs]
  have hm : (a.cycle σ).mems = (b.cycle σ).mems := by
    simp only [Module.cycle]
    exact memCycleFold_eq σ hmems _
  exact St.eq_of_fields hr hm

/-- `Matches` implies equality of the formal transition systems. -/
theorem Module.Matches.toTSys_eq {a b : Module} (h : a.Matches b) :
    a.toTSys = b.toTSys := by
  have hi : (fun σ => σ = a.reset) = (fun σ => σ = b.reset) := by
    rw [h.reset_eq]
  have hc : a.cycle = b.cycle := funext h.cycle_eq
  unfold Module.toTSys
  rw [hi, hc]

end Loom.Emit.MicroVerilog
