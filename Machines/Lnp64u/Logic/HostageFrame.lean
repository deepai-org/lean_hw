-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Logic.HostageMeasure

/-!
# T6 foreign-cycle frames

A cycle whose actor is *not* the chain head leaves the blocked caller's
chain — the gate list, the head, every chain activation, the payer walk,
and the origin's budget — untouched (`FrozenStep`). One lemma per shape of
the classification (`ChainOut`/`CallShape`/`RetShape`/`HaltShape`/
`IssueShape`), each by excluding the actor, its served gate, and any
resumed caller from the chain members / descent visits.
-/

namespace Machines.Lnp64u

open Loom

/-- Everything the T6 counting needs preserved across a non-head cycle. -/
structure FrozenStep (d : DomainId) (l : List GateId) (h : DomainId)
    (X X' : MachineState) : Prop where
  run_d : (X'.doms d).run = (X.doms d).run
  chain : ChainFrom X' d l h
  acts : ∀ g' ∈ l, (X'.gates g').act = (X.gates g').act
  payer : X'.payer d = X.payer d
  budget_o : (X'.doms (X.payer d)).budget = (X.doms (X.payer d)).budget

/-! ## Membership helpers -/

/-- Every chain gate has a live activation. -/
theorem ChainFrom.gates_act {σ : MachineState} (hwf : Wf σ) {x : DomainId}
    {l : List GateId} {h : DomainId} (hcf : ChainFrom σ x l h) :
    ∀ g' ∈ l, ∃ a, (σ.gates g').act = some a := by
  induction hcf with
  | top _ => intro g' hg'; exact absurd hg' (List.not_mem_nil)
  | link hb hrest ih =>
      rename_i x' g rest h'
      intro g' hg'
      rcases List.mem_cons.mp hg' with h1 | h1
      · subst h1
        obtain ⟨a, ha, _⟩ := hwf.blocked_gate x' g' hb
        exact ⟨a, ha⟩
      · exact ih g' h1

/-- Every chain gate's callee is a member. -/
theorem ChainFrom.callee_mem {σ : MachineState} {x : DomainId}
    {l : List GateId} {h : DomainId} (_hcf : ChainFrom σ x l h) :
    ∀ g' ∈ l, gateCallee σ g' ∈ chainMembers σ x l := by
  intro g' hg'
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem hg')

/-- A running non-head domain is not a chain member. -/
theorem running_not_mem {σ : MachineState} {x : DomainId} {l : List GateId}
    {h : DomainId} (hcf : ChainFrom σ x l h) {e : DomainId}
    (hrun : (σ.doms e).run = .running) (hne : e ≠ h) :
    e ∉ chainMembers σ x l := by
  intro hmem
  rcases hcf.mem_run e hmem with h1 | ⟨gy, _, h1⟩
  · exact hne h1
  · rw [h1] at hrun
    exact absurd hrun (by simp)

/-- A running non-head domain's served gate is not a chain gate. -/
theorem running_gate_not_mem {σ : MachineState} (hwf : Wf σ) {x : DomainId}
    {l : List GateId} {h : DomainId} (hcf : ChainFrom σ x l h) {e : DomainId}
    {ge : GateId} (hserv : (σ.doms e).serving = some ge)
    (hrun : (σ.doms e).run = .running) (hne : e ≠ h) : ge ∉ l := by
  intro hmem
  have hcal : gateCallee σ ge = e := (hwf.serving_gate e ge hserv).1
  have := hcf.callee_mem ge hmem
  rw [hcal] at this
  exact running_not_mem hcf hrun hne this

/-- A domain blocked on a non-chain gate is not a chain member. -/
theorem blocked_outside_not_mem {σ : MachineState} {x : DomainId}
    {l : List GateId} {h : DomainId} (hcf : ChainFrom σ x l h) {c : DomainId}
    {gc : GateId} (hbc : (σ.doms c).run = .blocked gc) (hgc : gc ∉ l) :
    c ∉ chainMembers σ x l := by
  intro hmem
  rcases hcf.mem_run c hmem with h1 | ⟨gy, hgy, h1⟩
  · rw [h1] at hbc
    rw [hcf.top_running] at hbc
    exact absurd hbc (by simp)
  · rw [h1] at hbc
    injection hbc with hE
    exact hgc (hE ▸ hgy)

/-- Every descent-visited domain is blocked (given a blocked start). -/
theorem descMem_blocked {σ : MachineState} (hwf : Wf σ) {x : DomainId}
    {gx : GateId} (hbx : (σ.doms x).run = .blocked gx) :
    ∀ y, DescMem σ x y → ∃ gy, (σ.doms y).run = .blocked gy := by
  intro y hy
  induction hy with
  | refl => exact ⟨gx, hbx⟩
  | step _ hs ha => exact ⟨_, (hwf.gate_serving _ _ ha).2.1⟩

/-- A visited gate's callee is the visitor: gates served by running domains
are never visited. -/
theorem descMem_gate_ne {σ : MachineState} (hwf : Wf σ) {x : DomainId}
    {gx : GateId} (hbx : (σ.doms x).run = .blocked gx) {e : DomainId}
    (hrun : (σ.doms e).run = .running) :
    ∀ y gv, DescMem σ x y → (σ.doms y).serving = some gv →
    ∀ {ge : GateId}, (σ.doms e).serving = some ge → gv ≠ ge := by
  intro y gv hy hsv ge hse hE
  subst hE
  have h1 : (σ.gates gv).config.callee = y := (hwf.serving_gate y gv hsv).1
  have h2 : (σ.gates gv).config.callee = e := (hwf.serving_gate e gv hse).1
  obtain ⟨gy, hgy⟩ := descMem_blocked hwf hbx y hy
  rw [h1.symm.trans h2] at hgy
  rw [hgy] at hrun
  exact absurd hrun (by simp)

/-- No visited domain is running. -/
theorem descMem_not_running {σ : MachineState} (hwf : Wf σ) {x : DomainId}
    {gx : GateId} (hbx : (σ.doms x).run = .blocked gx) {e : DomainId}
    (hrun : (σ.doms e).run = .running) : ∀ y, DescMem σ x y → y ≠ e := by
  intro y hy hE
  obtain ⟨gy, hgy⟩ := descMem_blocked hwf hbx y hy
  exact absurd (hrun.symm.trans (hE ▸ hgy)) (by simp)

/-- The origin is blocked whenever the descent starts blocked. -/
theorem descends_blocked {σ : MachineState} (hwf : Wf σ) {x o : DomainId}
    (hdes : Descends σ x o) :
    (∃ gx, (σ.doms x).run = .blocked gx) → ∃ go, (σ.doms o).run = .blocked go := by
  induction hdes with
  | refl _ => exact fun hx => hx
  | step hs ha hdes' ih => exact fun _ => ih ⟨_, (hwf.gate_serving _ _ ha).2.1⟩

/-! ## Per-shape frozen steps

Context: `X` well-formed with `DepthLink`, `d` blocked with chain
`(l, h)`. The actor `e` runs and is not the head. -/

/-- The payer walk survives any transition that (i) preserves the serving
mark of every blocked domain and (ii) preserves the activation of every
gate served by a blocked domain. -/
theorem payer_frame_of {X X' : MachineState} (hwf : Wf X)
    {d : DomainId} {gd : GateId} (hb : (X.doms d).run = .blocked gd)
    (hs : ∀ y gy, (X.doms y).run = .blocked gy →
      (X'.doms y).serving = (X.doms y).serving)
    (hg : ∀ y gy gv, (X.doms y).run = .blocked gy → (X.doms y).serving = some gv →
      (X'.gates gv).act = (X.gates gv).act) :
    X'.payer d = X.payer d := by
  refine chainOrigin_congr maxChainDepth d ?_ ?_
  · intro y hy
    obtain ⟨gy, hgy⟩ := descMem_blocked hwf hb y hy
    exact hs y gy hgy
  · intro y gv hy hsv
    obtain ⟨gy, hgy⟩ := descMem_blocked hwf hb y hy
    exact hg y gy gv hgy hsv

/-- The origin (a blocked domain) is never the running actor. -/
theorem payer_ne_actor {X : MachineState} (hwf : Wf X) (hdl : DepthLink X)
    {d : DomainId} {gd : GateId} (hb : (X.doms d).run = .blocked gd)
    {e : DomainId} (hrune : (X.doms e).run = .running) : X.payer d ≠ e := by
  intro hE
  obtain ⟨hdes, _⟩ := payer_descends hwf hdl d
  obtain ⟨go, hgo⟩ := descends_blocked hwf hdes ⟨gd, hb⟩
  have : (X.doms e).run = .blocked go := hE ▸ hgo
  rw [this] at hrune
  exact absurd hrune (by simp)

/-- Foreign `ChainOut` (a calm op, or any err outcome) freezes everything. -/
theorem FrozenStep.of_chainOut {X X' : MachineState} (hwf : Wf X) (hdl : DepthLink X)
    {d : DomainId} {gd : GateId} (hb : (X.doms d).run = .blocked gd)
    {l : List GateId} {h : DomainId} (hcf : ChainFrom X d l h)
    {e : DomainId} (hco : ChainOut e X X')
    (hrune : (X.doms e).run = .running) : FrozenStep d l h X X' := by
  obtain ⟨hg, hr, hs, hm, hbud⟩ := hco
  refine ⟨hr d, ?_, ?_, ?_, ?_⟩
  · exact hcf.frame (fun g' _ => by unfold gateCallee; rw [hg]) (fun y _ => hr y)
  · intro g' _
    rw [hg]
  · exact payer_frame_of hwf hb (fun y gy _ => hs y) (fun y gy gv _ _ => by rw [hg])
  · exact hbud _ (payer_ne_actor hwf hdl hb hrune)

/-- Foreign `gate_call` retiring: the fresh gate and the newly serving
callee sit outside the chain and the descent. -/
theorem FrozenStep.of_callShape {X X' : MachineState} (hwf : Wf X) (hdl : DepthLink X)
    {d : DomainId} {gd : GateId} (hb : (X.doms d).run = .blocked gd)
    {l : List GateId} {h : DomainId} (hcf : ChainFrom X d l h)
    {e : DomainId} (hsh : CallShape e X X')
    (hrune : (X.doms e).run = .running) (hne : e ≠ h) : FrozenStep d l h X X' := by
  obtain ⟨gid, act, hgnone, hcalne, hcalrun, hcalserv, hcaller, hdepth, hdle, hdon,
    hgo, hga, hgc, hmax, hbudo, hso, hsc, hro, hrb⟩ := hsh
  -- the fresh gate is not a chain gate (chain gates have live activations)
  have hgid_l : gid ∉ l := by
    intro hmem
    obtain ⟨a', ha'⟩ := hcf.gates_act hwf gid hmem
    rw [hgnone] at ha'
    exact absurd ha' (by simp)
  -- the actor is not a member
  have hemem := running_not_mem hcf hrune hne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hro d (fun hE => hemem (hE ▸ List.mem_cons_self))
  · refine hcf.frame ?_ ?_
    · intro g' hg'
      unfold gateCallee
      rw [congrArg GateState.config (hgo g' (fun hE => hgid_l (hE ▸ hg')))]
    · intro y hy
      exact hro y (fun hE => hemem (hE ▸ hy))
  · intro g' hg'
    rw [hgo g' (fun hE => hgid_l (hE ▸ hg'))]
  · refine payer_frame_of hwf hb ?_ ?_
    · intro y gy hgy
      refine hso y ?_
      intro hE
      exact absurd (hcalrun.symm.trans (hE ▸ hgy)) (by simp)
    · intro y gy gv hgy hsv
      have hne' : gv ≠ gid := by
        intro hE
        subst hE
        have := (hwf.serving_gate y gv hsv).2
        rw [hgnone] at this
        exact absurd this (by simp)
      rw [hgo gv hne']
  · exact hbudo _ (payer_ne_actor hwf hdl hb hrune)

/-- Foreign `gate_return` retiring: the freed gate and the resumed caller
sit outside the chain and the descent. -/
theorem FrozenStep.of_retShape {X X' : MachineState} (hwf : Wf X) (hdl : DepthLink X)
    {d : DomainId} {gd : GateId} (hb : (X.doms d).run = .blocked gd)
    {l : List GateId} {h : DomainId} (hcf : ChainFrom X d l h)
    {e : DomainId} (hsh : RetShape e X X')
    (hrune : (X.doms e).run = .running) (hne : e ≠ h) : FrozenStep d l h X X' := by
  obtain ⟨gid, act, hserv, hact, hgo, hga, hgc, hmax, hbudo, hso, hsd, hro, hrc⟩ := hsh
  have hgid_l : gid ∉ l := running_gate_not_mem hwf hcf hserv hrune hne
  have hcblk : (X.doms act.caller).run = .blocked gid := (hwf.gate_serving gid act hact).2.1
  have hcmem : act.caller ∉ chainMembers X d l := blocked_outside_not_mem hcf hcblk hgid_l
  have hemem := running_not_mem hcf hrune hne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hro d (fun hE => hcmem (hE ▸ List.mem_cons_self))
  · refine hcf.frame ?_ ?_
    · intro g' hg'
      unfold gateCallee
      rw [congrArg GateState.config (hgo g' (fun hE => hgid_l (hE ▸ hg')))]
    · intro y hy
      exact hro y (fun hE => hcmem (hE ▸ hy))
  · intro g' hg'
    rw [hgo g' (fun hE => hgid_l (hE ▸ hg'))]
  · refine payer_frame_of hwf hb ?_ ?_
    · intro y gy hgy
      refine hso y ?_
      intro hE
      exact absurd (hrune.symm.trans (hE ▸ hgy)) (by simp)
    · intro y gy gv hgy hsv
      have hne' : gv ≠ gid := by
        intro hE
        subst hE
        have h1 : (X.gates gv).config.callee = y := (hwf.serving_gate y gv hsv).1
        have h2 : (X.gates gv).config.callee = e := (hwf.serving_gate e gv hserv).1
        have hye : y = e := h1.symm.trans h2
        exact absurd (hrune.symm.trans (hye ▸ hgy)) (by simp)
      rw [hgo gv hne']
  · exact hbudo _ (payer_ne_actor hwf hdl hb hrune)

/-- Foreign halt (fault, voluntary, or donation exhaustion): the halted
actor, its freed gate, and any resumed caller sit outside the chain. -/
theorem FrozenStep.of_haltShape {X X' : MachineState} (hwf : Wf X) (hdl : DepthLink X)
    {d : DomainId} {gd : GateId} (hb : (X.doms d).run = .blocked gd)
    {l : List GateId} {h : DomainId} (hcf : ChainFrom X d l h)
    {e : DomainId} (hsh : HaltShape e X X')
    (hrune : (X.doms e).run = .running) (hne : e ≠ h) : FrozenStep d l h X X' := by
  obtain ⟨hmax, hbudo, hrh, hsdnone, hso, hcase⟩ := hsh
  have hemem := running_not_mem hcf hrune hne
  have hserv_frame : ∀ y gy, (X.doms y).run = .blocked gy →
      (X'.doms y).serving = (X.doms y).serving := by
    intro y gy hgy
    refine hso y ?_
    intro hE
    exact absurd (hrune.symm.trans (hE ▸ hgy)) (by simp)
  rcases hcase with ⟨hgeq, hro⟩ | ⟨g, a, hsg, hag, hacne, hgo, hga, hgc, hcr, hro⟩
  · refine ⟨hro d (fun hE => hemem (hE ▸ List.mem_cons_self)), ?_, ?_, ?_, ?_⟩
    · exact hcf.frame (fun g' _ => by unfold gateCallee; rw [hgeq])
        (fun y hy => hro y (fun hE => hemem (hE ▸ hy)))
    · intro g' _
      rw [hgeq]
    · exact payer_frame_of hwf hb hserv_frame (fun y gy gv _ _ => by rw [hgeq])
    · exact hbudo _ (payer_ne_actor hwf hdl hb hrune)
  · have hg_l : g ∉ l := running_gate_not_mem hwf hcf hsg hrune hne
    have hcblk : (X.doms a.caller).run = .blocked g := (hwf.gate_serving g a hag).2.1
    have hcmem : a.caller ∉ chainMembers X d l := blocked_outside_not_mem hcf hcblk hg_l
    refine ⟨hro d (fun hE => hemem (hE ▸ List.mem_cons_self))
        (fun hE => hcmem (hE ▸ List.mem_cons_self)), ?_, ?_, ?_, ?_⟩
    · refine hcf.frame ?_ ?_
      · intro g' hg'
        unfold gateCallee
        rw [congrArg GateState.config (hgo g' (fun hE => hg_l (hE ▸ hg')))]
      · intro y hy
        exact hro y (fun hE => hemem (hE ▸ hy)) (fun hE => hcmem (hE ▸ hy))
    · intro g' hg'
      rw [hgo g' (fun hE => hg_l (hE ▸ hg'))]
    · refine payer_frame_of hwf hb hserv_frame ?_
      intro y gy gv hgy hsv
      have hne' : gv ≠ g := by
        intro hE
        subst hE
        have h1 : (X.gates gv).config.callee = y := (hwf.serving_gate y gv hsv).1
        have h2 : (X.gates gv).config.callee = e := (hwf.serving_gate e gv hsg).1
        have hye : y = e := h1.symm.trans h2
        exact absurd (hrune.symm.trans (hye ▸ hgy)) (by simp)
      rw [hgo gv hne']
    · exact hbudo _ (payer_ne_actor hwf hdl hb hrune)

/-- Foreign issue: only a non-origin budget and (possibly) a non-chain
gate's donation move. -/
theorem FrozenStep.of_issueShape {X X' : MachineState} (hwf : Wf X) (hdl : DepthLink X)
    {d : DomainId} {gd : GateId} (hb : (X.doms d).run = .blocked gd)
    {l : List GateId} {h : DomainId} (hcf : ChainFrom X d l h)
    {e p : DomainId} {c : Nat} (hsh : IssueShape e p c X X')
    (hrune : (X.doms e).run = .running) (hne : e ≠ h)
    (hpe : p = X.payer e) : FrozenStep d l h X X' := by
  obtain ⟨hro, hso, hmax, hbp, hbo, hgates⟩ := hsh
  have hpne : p ≠ X.payer d := by
    intro hE
    exact hne (running_payer_eq_top hwf hdl hcf e hrune (hpe ▸ hE))
  have hacts : ∀ g' ∈ l, (X'.gates g').act = (X.gates g').act := by
    intro g' hg'
    rcases hgates with ⟨_, hgeq⟩ | ⟨g, a, hsv, hag, hdon, hgo, hga, hgc⟩
    · rw [hgeq]
    · have hne' : g' ≠ g := by
        intro hE
        exact running_gate_not_mem hwf hcf hsv hrune hne (hE ▸ hg')
      rw [hgo g' hne']
  have hconf : ∀ g', (X'.gates g').config = (X.gates g').config := by
    intro g'
    rcases hgates with ⟨_, hgeq⟩ | ⟨g, a, hsv, hag, hdon, hgo, hga, hgc⟩
    · rw [hgeq]
    · by_cases hE : g' = g
      · subst hE
        exact hgc
      · rw [hgo g' hE]
  refine ⟨hro d, ?_, hacts, ?_, ?_⟩
  · exact hcf.frame (fun g' _ => by unfold gateCallee; rw [hconf g']) (fun y _ => hro y)
  · refine payer_frame_of hwf hb (fun y gy _ => hso y) ?_
    intro y gy gv hgy hsv
    rcases hgates with ⟨_, hgeq⟩ | ⟨g, a, hsvg, hag, hdon, hgo, hga, hgc⟩
    · rw [hgeq]
    · have hne' : gv ≠ g := by
        intro hE
        subst hE
        have h1 : (X.gates gv).config.callee = y := (hwf.serving_gate y gv hsv).1
        have h2 : (X.gates gv).config.callee = e := (hwf.serving_gate e gv hsvg).1
        have hye : y = e := h1.symm.trans h2
        exact absurd (hrune.symm.trans (hye ▸ hgy)) (by simp)
      rw [hgo gv hne']
  · exact hbo _ (Ne.symm hpne)

/-- Doms- and gates-preserving glue (burn, Mover, the cycle bump) freezes
everything. -/
theorem FrozenStep.of_eq_parts {X X' : MachineState}
    {d : DomainId} {l : List GateId} {h : DomainId}
    (hcf : ChainFrom X d l h)
    (hd : X'.doms = X.doms) (hg : X'.gates = X.gates) : FrozenStep d l h X X' := by
  refine ⟨by rw [hd], ?_, ?_, ?_, by rw [hd]⟩
  · exact hcf.frame (fun g' _ => by unfold gateCallee; rw [hg]) (fun y _ => by rw [hd])
  · intro g' _
    rw [hg]
  · exact chainOrigin_congr maxChainDepth d (fun y _ => by rw [hd])
      (fun y gv _ _ => by rw [hg])

/-- `FrozenStep` composes. -/
theorem FrozenStep.trans {X X' X'' : MachineState}
    {d : DomainId} {l : List GateId} {h : DomainId}
    (h1 : FrozenStep d l h X X') (h2 : FrozenStep d l h X' X'') :
    FrozenStep d l h X X'' := by
  refine ⟨h2.run_d.trans h1.run_d, h2.chain, ?_, h2.payer.trans h1.payer, ?_⟩
  · intro g' hg'
    exact (h2.acts g' hg').trans (h1.acts g' hg')
  · have hb2 := h2.budget_o
    rw [h1.payer] at hb2
    exact hb2.trans h1.budget_o

end Machines.Lnp64u
