import Machines.Lnp64u.Logic.Hostage

/-!
# T6 chain structure (obligation 1: the frozen path)

The serving chain above a blocked caller, as a deterministic relation
(`ChainFrom`), with:

* **existence** — under `Wf` + `HaltedServingNone` + `DepthLink`, every
  blocked domain's chain is a finite path of length ≤ `maxChainDepth`
  ending at a *running* head (`chain_exists`);
* **determinism** — `run` is a function, so the chain is unique
  (`ChainFrom.unique`);
* **payer structure** — the payer walk (`chainOrigin`) lands on a
  serving-free origin, is fuel-stable, and is constant along the chain
  (`payer_descends`, `payer_chain`);
* **head uniqueness** — the head is the *only* running domain whose payer
  is the origin (`running_payer_eq_top`): the fact that makes the origin's
  budget drainable only by chain issues;
* **frames** — the chain and the payer walk depend only on the runs of the
  members, the callee configs of the member gates, and the servings/acts
  along the descent (`ChainFrom.frame`, `chainOrigin_congr`) — the
  transport used to freeze the chain across foreign cycles.
-/

namespace Machines.Lnp64u

open Loom

/-- The callee of a gate (configs are boot-immutable). -/
def gateCallee (σ : MachineState) (g : GateId) : DomainId :=
  (σ.gates g).config.callee

/-- The serving chain above `x`: `ChainFrom σ x l h` — `x` is blocked on the
first gate of `l`, each gate's callee is blocked on the next, and the last
gate's callee is the running head `h` (`l = []` iff `x` itself runs). -/
inductive ChainFrom (σ : MachineState) : DomainId → List GateId → DomainId → Prop
  | top {x} : (σ.doms x).run = .running → ChainFrom σ x [] x
  | link {x g rest h} : (σ.doms x).run = .blocked g →
      ChainFrom σ (gateCallee σ g) rest h → ChainFrom σ x (g :: rest) h

/-- The domains on the chain: the start plus every gate's callee. -/
def chainMembers (σ : MachineState) (x : DomainId) (l : List GateId) : List DomainId :=
  x :: l.map (gateCallee σ)

/-- `run` is a function, so the chain is unique. -/
theorem ChainFrom.unique {σ : MachineState} {x : DomainId} {l1 l2 : List GateId}
    {h1 h2 : DomainId} (hc1 : ChainFrom σ x l1 h1) (hc2 : ChainFrom σ x l2 h2) :
    l1 = l2 ∧ h1 = h2 := by
  induction hc1 generalizing l2 h2 with
  | top hrun =>
      cases hc2 with
      | top _ => exact ⟨rfl, rfl⟩
      | link hb _ => rw [hrun] at hb; exact absurd hb (by simp)
  | link hb hrest ih =>
      cases hc2 with
      | top hrun => rw [hrun] at hb; exact absurd hb (by simp)
      | link hb2 hrest2 =>
          rename_i g rest h g2 rest2
          have hg : g = g2 := by
            rw [hb] at hb2
            injection hb2
          subst hg
          obtain ⟨hl, hh⟩ := ih hrest2
          exact ⟨by rw [hl], hh⟩

/-- The head runs. -/
theorem ChainFrom.top_running {σ : MachineState} {x : DomainId} {l : List GateId}
    {h : DomainId} (hc : ChainFrom σ x l h) : (σ.doms h).run = .running := by
  induction hc with
  | top hrun => exact hrun
  | link _ _ ih => exact ih

/-- The head is a member. -/
theorem ChainFrom.top_mem {σ : MachineState} {x : DomainId} {l : List GateId}
    {h : DomainId} (hc : ChainFrom σ x l h) : h ∈ chainMembers σ x l := by
  induction hc with
  | top _ => exact List.mem_singleton.mpr rfl
  | link _ _ ih =>
      unfold chainMembers at ih ⊢
      simp only [List.map_cons]
      rcases List.mem_cons.mp ih with h' | h'
      · exact List.mem_cons_of_mem _ (h' ▸ List.mem_cons_self)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')

/-- Every member is the running head or blocked on a chain gate. -/
theorem ChainFrom.mem_run {σ : MachineState} {x : DomainId} {l : List GateId}
    {h : DomainId} (hc : ChainFrom σ x l h) :
    ∀ y ∈ chainMembers σ x l, y = h ∨ ∃ gy ∈ l, (σ.doms y).run = .blocked gy := by
  induction hc with
  | top hrun =>
      intro y hy
      rw [List.mem_singleton.mp hy]
      exact .inl rfl
  | link hb hrest ih =>
      rename_i x' g rest h'
      intro y hy
      unfold chainMembers at hy
      simp only [List.map_cons] at hy
      rcases List.mem_cons.mp hy with h1 | h1
      · subst h1
        exact .inr ⟨g, List.mem_cons_self, hb⟩
      · rcases ih y h1 with h2 | ⟨gy, hgy, h2⟩
        · exact .inl h2
        · exact .inr ⟨gy, List.mem_cons_of_mem _ hgy, h2⟩

/-- Chasing a blocked member's gate stays inside the chain. -/
theorem ChainFrom.mem_next {σ : MachineState} {z : DomainId} {L : List GateId}
    {h : DomainId} (hc : ChainFrom σ z L h) :
    ∀ y ∈ chainMembers σ z L, ∀ gy, (σ.doms y).run = .blocked gy →
      gy ∈ L ∧ gateCallee σ gy ∈ chainMembers σ z L := by
  induction hc with
  | top hrun =>
      intro y hy gy hby
      rw [List.mem_singleton.mp hy] at hby
      rw [hrun] at hby
      exact absurd hby (by simp)
  | link hb hrest ih =>
      rename_i x' g rest h'
      intro y hy gy hby
      unfold chainMembers at hy ⊢
      simp only [List.map_cons] at hy ⊢
      rcases List.mem_cons.mp hy with h1 | h1
      · subst h1
        rw [hb] at hby
        injection hby with hgy
        subst hgy
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      · obtain ⟨hmem, hnext⟩ := ih y h1 gy hby
        exact ⟨List.mem_cons_of_mem _ hmem, List.mem_cons_of_mem _ hnext⟩

/-- Chain existence: the ascent from a blocked domain terminates at a running
head within the depth budget (depths increment, `DepthLink`, and are capped
at `maxChainDepth`, `Wf.gate_serving`). -/
theorem chain_exists_aux {σ : MachineState} (hwf : Wf σ) (hsn : HaltedServingNone σ)
    (hdl : DepthLink σ) : ∀ (fuel : Nat) (x : DomainId) (g : GateId) (a : Activation),
    (σ.doms x).run = .blocked g → (σ.gates g).act = some a →
    maxChainDepth < a.depth + fuel →
    ∃ l h, ChainFrom σ x l h ∧ l.length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro x g a hb ha hlt
      have := (hwf.gate_serving g a ha).2.2.2
      omega
  | succ f ih =>
      intro x g a hb ha hlt
      have hserv : (σ.doms (gateCallee σ g)).serving = some g :=
        (hwf.gate_serving g a ha).1
      cases hy : (σ.doms (gateCallee σ g)).run with
      | running =>
          exact ⟨[g], gateCallee σ g, .link hb (.top hy), by simp⟩
      | halted =>
          have := hsn _ hy
          rw [hserv] at this
          exact absurd this (by simp)
      | blocked g2 =>
          obtain ⟨a2, ha2, hc2⟩ := hwf.blocked_gate _ g2 hy
          have hdep : a2.depth = a.depth + 1 :=
            (hdl g2 a2 ha2).2 g a (by rw [hc2]; exact hserv) ha
          obtain ⟨l, hh, hcf, hlen⟩ := ih (gateCallee σ g) g2 a2 hy ha2 (by omega)
          exact ⟨g :: l, hh, .link hb hcf, by simpa using Nat.succ_le_succ hlen⟩

/-- The chain of a blocked domain exists and has length ≤ `maxChainDepth`. -/
theorem chain_exists {σ : MachineState} (hwf : Wf σ) (hsn : HaltedServingNone σ)
    (hdl : DepthLink σ) {d : DomainId} {g : GateId} (hb : (σ.doms d).run = .blocked g) :
    ∃ l h, ChainFrom σ d l h ∧ l.length ≤ maxChainDepth := by
  obtain ⟨a, ha, _⟩ := hwf.blocked_gate d g hb
  have h1 : 1 ≤ a.depth := (hwf.gate_serving g a ha).2.2.1
  exact chain_exists_aux hwf hsn hdl maxChainDepth d g a hb ha (by omega)

/-- The head serves the last chain gate. -/
theorem ChainFrom.head_serving {σ : MachineState} (hwf : Wf σ) {x : DomainId}
    {l : List GateId} {h : DomainId} (hc : ChainFrom σ x l h) (hne : l ≠ []) :
    (σ.doms h).serving = some (l.getLast hne) := by
  induction hc with
  | top _ => exact absurd rfl hne
  | link hb hrest ih =>
      rename_i x' g rest h'
      cases hrest with
      | top hrun =>
          obtain ⟨a, ha, _⟩ := hwf.blocked_gate x' g hb
          simpa using (hwf.gate_serving g a ha).1
      | link hb2 hrest2 =>
          rename_i g2 rest2
          have := ih (by simp)
          simpa [List.getLast_cons] using this

/-! ## The payer walk -/

/-- The descent depth of `x`: how many caller-links `chainOrigin` must
follow (0 when `x` serves nobody). -/
def descentDepth (σ : MachineState) (x : DomainId) : Nat :=
  match (σ.doms x).serving with
  | none => 0
  | some g =>
      match (σ.gates g).act with
      | some a => a.depth
      | none => 0

theorem chainOrigin_of_none {σ : MachineState} {x : DomainId}
    (h : (σ.doms x).serving = none) : ∀ fuel, σ.chainOrigin fuel x = x := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ f =>
      unfold MachineState.chainOrigin
      rw [h]

theorem chainOrigin_succ_serving {σ : MachineState} {x : DomainId} {g : GateId}
    {a : Activation} (hs : (σ.doms x).serving = some g)
    (ha : (σ.gates g).act = some a) (f : Nat) :
    σ.chainOrigin (f + 1) x = σ.chainOrigin f a.caller := by
  show (match (σ.doms x).serving with
        | none => x
        | some g1 =>
            match (σ.gates g1).act with
            | some a1 => σ.chainOrigin f a1.caller
            | none => x) = σ.chainOrigin f a.caller
  rw [hs]
  simp only [ha]

/-- Downward reachability along the caller links. -/
inductive Descends (σ : MachineState) : DomainId → DomainId → Prop
  | refl {x} : (σ.doms x).serving = none → Descends σ x x
  | step {x g a y} : (σ.doms x).serving = some g → (σ.gates g).act = some a →
      Descends σ a.caller y → Descends σ x y

/-- One caller-link drops the descent depth. -/
theorem descentDepth_caller {σ : MachineState} (hwf : Wf σ) (hdl : DepthLink σ)
    {x : DomainId} {g : GateId} {a : Activation}
    (hs : (σ.doms x).serving = some g) (ha : (σ.gates g).act = some a) :
    descentDepth σ a.caller + 1 = a.depth := by
  cases hs' : (σ.doms a.caller).serving with
  | none =>
      have := (hdl g a ha).1 hs'
      simp only [descentDepth, hs']
      omega
  | some g' =>
      cases ha' : (σ.gates g').act with
      | none =>
          have := (hwf.serving_gate a.caller g' hs').2
          rw [ha'] at this
          simp at this
      | some a' =>
          have := (hdl g a ha).2 g' a' hs' ha'
          simp only [descentDepth, hs', ha']
          omega

/-- The payer walk: lands on a serving-free origin, is reached by a descent,
and is fuel-irrelevant beyond the descent depth. -/
theorem chainOrigin_spec {σ : MachineState} (hwf : Wf σ) (hdl : DepthLink σ) :
    ∀ (n : Nat) (x : DomainId) (fuel : Nat),
    descentDepth σ x ≤ n → n ≤ fuel →
    Descends σ x (σ.chainOrigin fuel x) ∧
    (σ.doms (σ.chainOrigin fuel x)).serving = none ∧
    (∀ fuel', n ≤ fuel' → σ.chainOrigin fuel' x = σ.chainOrigin fuel x) := by
  intro n
  induction n with
  | zero =>
      intro x fuel hd _
      cases hs : (σ.doms x).serving with
      | none =>
          rw [chainOrigin_of_none hs]
          exact ⟨.refl hs, hs, fun fuel' _ => chainOrigin_of_none hs fuel'⟩
      | some g =>
          exfalso
          simp only [descentDepth, hs] at hd
          cases ha : (σ.gates g).act with
          | none =>
              have := (hwf.serving_gate x g hs).2
              rw [ha] at this
              simp at this
          | some a =>
              simp only [ha] at hd
              have := (hwf.gate_serving g a ha).2.2.1
              omega
  | succ k ih =>
      intro x fuel hd hf
      cases hs : (σ.doms x).serving with
      | none =>
          rw [chainOrigin_of_none hs]
          exact ⟨.refl hs, hs, fun fuel' _ => chainOrigin_of_none hs fuel'⟩
      | some g =>
          cases ha : (σ.gates g).act with
          | none =>
              exfalso
              have := (hwf.serving_gate x g hs).2
              rw [ha] at this
              simp at this
          | some a =>
              have hdx : descentDepth σ x = a.depth := by
                simp only [descentDepth, hs, ha]
              have hdc : descentDepth σ a.caller ≤ k := by
                have := descentDepth_caller hwf hdl hs ha
                omega
              obtain ⟨f', hf'⟩ : ∃ f', fuel = f' + 1 := by
                cases fuel with
                | zero => omega
                | succ f' => exact ⟨f', rfl⟩
              subst hf'
              rw [chainOrigin_succ_serving hs ha]
              obtain ⟨hdes, hserv, hirr⟩ := ih a.caller f' hdc (by omega)
              refine ⟨.step hs ha hdes, hserv, ?_⟩
              intro fuel' hfuel'
              obtain ⟨f'', hf''⟩ : ∃ f'', fuel' = f'' + 1 := by
                cases fuel' with
                | zero => omega
                | succ f'' => exact ⟨f'', rfl⟩
              subst hf''
              rw [chainOrigin_succ_serving hs ha]
              rw [hirr f'' (by omega), hirr f' (by omega)]

/-- The descent depth is at most `maxChainDepth` in a well-formed state. -/
theorem descentDepth_le {σ : MachineState} (hwf : Wf σ) (x : DomainId) :
    descentDepth σ x ≤ maxChainDepth := by
  cases hs : (σ.doms x).serving with
  | none => simp only [descentDepth, hs]; exact Nat.zero_le _
  | some g =>
      cases ha : (σ.gates g).act with
      | none => simp only [descentDepth, hs, ha]; exact Nat.zero_le _
      | some a =>
          simp only [descentDepth, hs, ha]
          exact (hwf.gate_serving g a ha).2.2.2

/-- The payer is reached by a descent and serves nobody. -/
theorem payer_descends {σ : MachineState} (hwf : Wf σ) (hdl : DepthLink σ) (x : DomainId) :
    Descends σ x (σ.payer x) ∧ (σ.doms (σ.payer x)).serving = none := by
  obtain ⟨h1, h2, _⟩ := chainOrigin_spec hwf hdl maxChainDepth x maxChainDepth
    (descentDepth_le hwf x) (Nat.le_refl _)
  exact ⟨h1, h2⟩

/-- Payers are constant along a chain link. -/
theorem payer_link {σ : MachineState} (hwf : Wf σ) (hdl : DepthLink σ)
    {x : DomainId} {g : GateId} (hb : (σ.doms x).run = .blocked g) :
    σ.payer (gateCallee σ g) = σ.payer x := by
  obtain ⟨a, ha, hc⟩ := hwf.blocked_gate x g hb
  have hserv : (σ.doms (gateCallee σ g)).serving = some g := (hwf.gate_serving g a ha).1
  have hdep : a.depth ≤ maxChainDepth := (hwf.gate_serving g a ha).2.2.2
  have hdd : descentDepth σ x + 1 = a.depth := by
    rw [← hc]
    exact descentDepth_caller hwf hdl hserv ha
  obtain ⟨f, hfeq⟩ : ∃ f, maxChainDepth = f + 1 := ⟨3, rfl⟩
  show σ.chainOrigin maxChainDepth (gateCallee σ g) = σ.chainOrigin maxChainDepth x
  rw [hfeq, chainOrigin_succ_serving hserv ha, hc]
  obtain ⟨_, _, hirr⟩ := chainOrigin_spec hwf hdl (descentDepth σ x) x (f + 1)
    (Nat.le_refl _) (by omega)
  rw [hirr f (by omega)]

/-- The head's payer is the caller's payer: one budget funds the chain. -/
theorem payer_chain {σ : MachineState} (hwf : Wf σ) (hdl : DepthLink σ)
    {x : DomainId} {l : List GateId} {h : DomainId}
    (hc : ChainFrom σ x l h) : σ.payer h = σ.payer x := by
  induction hc with
  | top _ => rfl
  | link hb _ ih => exact ih.trans (payer_link hwf hdl hb)

/-- Splicing a descent below a chain: the origin's chain extends the
caller's chain, member-monotonically. -/
theorem descends_chainFrom {σ : MachineState} (hwf : Wf σ) {x o : DomainId}
    (hdes : Descends σ x o) :
    ∀ {lx : List GateId} {h : DomainId}, ChainFrom σ x lx h →
    ∃ L, ChainFrom σ o L h ∧
      ∀ y, y ∈ chainMembers σ x lx → y ∈ chainMembers σ o L := by
  induction hdes with
  | refl _ =>
      intro lx h hcf
      exact ⟨lx, hcf, fun y hy => hy⟩
  | @step z g a y hs ha hdes' ih =>
      intro lx h hcf
      have hcal : gateCallee σ g = z := (hwf.serving_gate z g hs).1
      have hblk : (σ.doms a.caller).run = .blocked g := (hwf.gate_serving g a ha).2.1
      have hcf2 : ChainFrom σ a.caller (g :: lx) h := .link hblk (by rw [hcal]; exact hcf)
      obtain ⟨L, hcfo, hsub⟩ := ih hcf2
      refine ⟨L, hcfo, fun y' hy' => hsub y' ?_⟩
      unfold chainMembers at hy' ⊢
      simp only [List.map_cons, hcal]
      exact List.mem_cons_of_mem _ hy'

/-- A domain descending to the chain's origin lies on the origin's chain. -/
theorem descends_mem {σ : MachineState} (hwf : Wf σ) {e o : DomainId}
    (hdes : Descends σ e o) :
    ∀ {L : List GateId} {h : DomainId}, ChainFrom σ o L h →
    e ∈ chainMembers σ o L := by
  induction hdes with
  | refl _ =>
      intro L h _
      exact List.mem_cons_self
  | @step z g a y hs ha hdes' ih =>
      intro L h hcf
      have hblk : (σ.doms a.caller).run = .blocked g := (hwf.gate_serving g a ha).2.1
      have hcal : gateCallee σ g = z := (hwf.serving_gate z g hs).1
      obtain ⟨_, hnext⟩ := hcf.mem_next a.caller (ih hcf) g hblk
      rw [hcal] at hnext
      exact hnext

/-- **Head uniqueness**: the chain head is the only *running* domain whose
payer is the blocked caller's payer. Every other issue in the machine
charges a budget other than the origin's. -/
theorem running_payer_eq_top {σ : MachineState} (hwf : Wf σ) (hdl : DepthLink σ)
    {d : DomainId} {l : List GateId} {h : DomainId}
    (hcf : ChainFrom σ d l h) (e : DomainId) (hrun : (σ.doms e).run = .running)
    (hpay : σ.payer e = σ.payer d) : e = h := by
  obtain ⟨hdes_d, _⟩ := payer_descends hwf hdl d
  obtain ⟨hdes_e, _⟩ := payer_descends hwf hdl e
  rw [hpay] at hdes_e
  obtain ⟨L, hcfo, _⟩ := descends_chainFrom hwf hdes_d hcf
  have he_mem : e ∈ chainMembers σ (σ.payer d) L := descends_mem hwf hdes_e hcfo
  rcases hcfo.mem_run e he_mem with h' | ⟨gy, _, hby⟩
  · exact h'
  · rw [hby] at hrun
    exact absurd hrun (by simp)

/-! ## Frames: the chain and the payer walk transport across agreeing states -/

/-- The chain transports across any transition preserving the members' runs
and the member gates' callees. -/
theorem ChainFrom.frame {σ σ' : MachineState} {x : DomainId} {l : List GateId}
    {h : DomainId} (hcf : ChainFrom σ x l h)
    (hconf : ∀ g ∈ l, gateCallee σ' g = gateCallee σ g)
    (hrun : ∀ y ∈ chainMembers σ x l, (σ'.doms y).run = (σ.doms y).run) :
    ChainFrom σ' x l h := by
  induction hcf with
  | top hr =>
      refine .top ?_
      rw [hrun _ List.mem_cons_self]
      exact hr
  | link hb hrest ih =>
      rename_i x' g rest h'
      refine .link ?_ ?_
      · rw [hrun x' List.mem_cons_self]
        exact hb
      · rw [hconf g List.mem_cons_self]
        refine ih (fun g' hg' => hconf g' (List.mem_cons_of_mem _ hg')) ?_
        intro y hy
        refine hrun y ?_
        unfold chainMembers at hy ⊢
        simp only [List.map_cons]
        rcases List.mem_cons.mp hy with h1 | h1
        · exact List.mem_cons_of_mem _ (h1 ▸ List.mem_cons_self)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)

/-- Downward membership: every domain the payer walk from `x` visits. -/
inductive DescMem (σ : MachineState) (x : DomainId) : DomainId → Prop
  | refl : DescMem σ x x
  | step {y g a} : DescMem σ x y → (σ.doms y).serving = some g →
      (σ.gates g).act = some a → DescMem σ x a.caller

theorem DescMem.lift {σ : MachineState} {x y : DomainId} {g : GateId} {a : Activation}
    (hs : (σ.doms x).serving = some g) (ha : (σ.gates g).act = some a)
    (h : DescMem σ a.caller y) : DescMem σ x y := by
  induction h with
  | refl => exact .step .refl hs ha
  | step hmem hs' ha' => exact .step (by assumption) hs' ha'

/-- The payer walk transports across any transition preserving the servings
of the visited domains and the acts of the visited gates. -/
theorem chainOrigin_congr {σ σ' : MachineState} :
    ∀ (fuel : Nat) (x : DomainId),
    (∀ y, DescMem σ x y → (σ'.doms y).serving = (σ.doms y).serving) →
    (∀ y g, DescMem σ x y → (σ.doms y).serving = some g →
      (σ'.gates g).act = (σ.gates g).act) →
    σ'.chainOrigin fuel x = σ.chainOrigin fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x _ _; rfl
  | succ f ih =>
      intro x hs hg
      show (match (σ'.doms x).serving with
            | none => x
            | some g1 =>
                match (σ'.gates g1).act with
                | some a1 => σ'.chainOrigin f a1.caller
                | none => x)
         = (match (σ.doms x).serving with
            | none => x
            | some g1 =>
                match (σ.gates g1).act with
                | some a1 => σ.chainOrigin f a1.caller
                | none => x)
      rw [hs x .refl]
      cases hserv : (σ.doms x).serving with
      | none => rfl
      | some g =>
          show (match (σ'.gates g).act with
                | some a1 => σ'.chainOrigin f a1.caller
                | none => x)
             = (match (σ.gates g).act with
                | some a1 => σ.chainOrigin f a1.caller
                | none => x)
          rw [hg x g .refl hserv]
          cases hact : (σ.gates g).act with
          | none => rfl
          | some a =>
              show σ'.chainOrigin f a.caller = σ.chainOrigin f a.caller
              exact ih a.caller
                (fun y hy => hs y (DescMem.lift hserv hact hy))
                (fun y g' hy hsy => hg y g' (DescMem.lift hserv hact hy) hsy)

end Machines.Lnp64u
