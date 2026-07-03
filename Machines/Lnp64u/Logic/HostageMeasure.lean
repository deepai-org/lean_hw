import Machines.Lnp64u.Logic.HostageChain

/-!
# T6 progress measure (obligation 2)

The radix measure over the blocked caller's chain: each chain gate
contributes `donated + 1` (so a *pop* — activation freed — strictly drops
the digit to 0) at radix weight `W ^ (maxChainDepth - position)` with
`W = maxDonationBound + 2` (so a parent's ≥ 1 donation charge dominates a
freshly pushed child's full digit). Chain events:

* head issue — the head's activation is drawn down: digit decrease at the
  last position (`measAux_lt_pointwise`);
* pop (`gate_return` retiring, forced unwind, head halt) — the new chain is
  a proper prefix with no digit raised (`measAux_prefix_lt`);
* push (`gate_call` retiring) — one fresh digit at the next weight, worth
  strictly less than the gate cost already charged at issue
  (`measAux_append`).

`chainMeasure` is the resulting `Nat`; its order type
`W ^ maxChainDepth` bounds the event count in `resumeBound`.
-/

namespace Machines.Lnp64u

open Loom

/-- The digit of gate `g`: `donated + 1` when live, 0 when free. -/
def actVal (σ : MachineState) (g : GateId) : Nat :=
  match (σ.gates g).act with
  | some a => a.donated + 1
  | none => 0

theorem actVal_congr {σ σ' : MachineState} {g : GateId}
    (h : (σ'.gates g).act = (σ.gates g).act) : actVal σ' g = actVal σ g := by
  unfold actVal
  rw [h]

theorem actVal_pos {σ : MachineState} {g : GateId} {a : Activation}
    (h : (σ.gates g).act = some a) : 1 ≤ actVal σ g := by
  simp only [actVal, h]
  omega

theorem actVal_none {σ : MachineState} {g : GateId}
    (h : (σ.gates g).act = none) : actVal σ g = 0 := by
  unfold actVal
  rw [h]

theorem actVal_le_of_donatedLe {m : Manifest} {σ : MachineState}
    (hd : DonatedLe m σ) (g : GateId) : actVal σ g ≤ maxDonationBound m + 1 := by
  cases ha : (σ.gates g).act with
  | none => simp only [actVal, ha]; omega
  | some a =>
      simp only [actVal, ha]
      have := hd g a ha
      omega

/-- The radix sum: first element at weight `W ^ e`, descending. -/
def measAux (W : Nat) (σ : MachineState) : Nat → List GateId → Nat
  | _, [] => 0
  | e, g :: rest => actVal σ g * W ^ e + measAux W σ (e - 1) rest

theorem measAux_congr {W : Nat} {σ σ' : MachineState} {l : List GateId}
    (h : ∀ g ∈ l, (σ'.gates g).act = (σ.gates g).act) :
    ∀ e, measAux W σ' e l = measAux W σ e l := by
  induction l with
  | nil => intro e; rfl
  | cons g rest ih =>
      intro e
      unfold measAux
      rw [actVal_congr (h g List.mem_cons_self),
          ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]

theorem measAux_le_pointwise {W : Nat} {σ σ' : MachineState} {l : List GateId}
    (h : ∀ g ∈ l, actVal σ' g ≤ actVal σ g) :
    ∀ e, measAux W σ' e l ≤ measAux W σ e l := by
  induction l with
  | nil => intro e; exact Nat.le_refl _
  | cons g rest ih =>
      intro e
      unfold measAux
      exact Nat.add_le_add
        (Nat.mul_le_mul_right _ (h g List.mem_cons_self))
        (ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) _)

theorem measAux_lt_pointwise {W : Nat} (hW : 0 < W) {σ σ' : MachineState}
    {l : List GateId} (h : ∀ g ∈ l, actVal σ' g ≤ actVal σ g) {g0 : GateId}
    (hmem : g0 ∈ l) (hlt : actVal σ' g0 < actVal σ g0) :
    ∀ e, measAux W σ' e l < measAux W σ e l := by
  induction l with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons g rest ih =>
      intro e
      unfold measAux
      rcases List.mem_cons.mp hmem with h1 | h1
      · subst h1
        exact Nat.add_lt_add_of_lt_of_le
          ((Nat.mul_lt_mul_right (Nat.pow_pos hW)).mpr hlt)
          (measAux_le_pointwise (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) _)
      · exact Nat.add_lt_add_of_le_of_lt
          (Nat.mul_le_mul_right _ (h g List.mem_cons_self))
          (ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) h1 _)

/-- A proper prefix with no digit raised is strictly below: the dropped
first suffix element was a live activation (digit ≥ 1). -/
theorem measAux_prefix_lt {W : Nat} (hW : 0 < W) {σ σ' : MachineState} :
    ∀ (l₁ : List GateId) (g0 : GateId) (l₂ : List GateId) (e : Nat),
    (∀ g ∈ l₁, actVal σ' g ≤ actVal σ g) → 1 ≤ actVal σ g0 →
    measAux W σ' e l₁ < measAux W σ e (l₁ ++ g0 :: l₂) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro g0 l₂ e _ hpos
      show 0 < actVal σ g0 * W ^ e + measAux W σ (e - 1) l₂
      have h1 : 1 * 1 ≤ actVal σ g0 * W ^ e := Nat.mul_le_mul hpos (Nat.pow_pos hW)
      omega
  | cons g rest ih =>
      intro g0 l₂ e h hpos
      show actVal σ' g * W ^ e + measAux W σ' (e - 1) rest <
        actVal σ g * W ^ e + measAux W σ (e - 1) (rest ++ g0 :: l₂)
      exact Nat.add_lt_add_of_le_of_lt
        (Nat.mul_le_mul_right _ (h g List.mem_cons_self))
        (ih g0 l₂ (e - 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) hpos)

/-- Appending one gate adds exactly its digit at the next weight. -/
theorem measAux_append {W : Nat} {σ : MachineState} :
    ∀ (l : List GateId) (gnew : GateId) (e : Nat),
    measAux W σ e (l ++ [gnew]) = measAux W σ e l + actVal σ gnew * W ^ (e - l.length) := by
  intro l
  induction l with
  | nil =>
      intro gnew e
      show actVal σ gnew * W ^ e + 0 = 0 + actVal σ gnew * W ^ (e - 0)
      rw [Nat.sub_zero]
      omega
  | cons g rest ih =>
      intro gnew e
      show actVal σ g * W ^ e + measAux W σ (e - 1) (rest ++ [gnew]) =
        actVal σ g * W ^ e + measAux W σ (e - 1) rest +
          actVal σ gnew * W ^ (e - (rest.length + 1))
      rw [ih gnew (e - 1)]
      have : e - 1 - rest.length = e - (rest.length + 1) := by omega
      rw [this]
      omega

/-- The radix bound: digits below `W - 1`, length within the weights. -/
theorem measAux_bound {W : Nat} (hW : 2 ≤ W) {σ : MachineState} :
    ∀ (l : List GateId) (e : Nat), (∀ g ∈ l, actVal σ g ≤ W - 1) →
    l.length ≤ e + 1 → measAux W σ e l ≤ W ^ (e + 1) - 1 := by
  intro l
  induction l with
  | nil =>
      intro e _ _
      show 0 ≤ W ^ (e + 1) - 1
      exact Nat.zero_le _
  | cons g rest ih =>
      intro e hv hlen
      show actVal σ g * W ^ e + measAux W σ (e - 1) rest ≤ W ^ (e + 1) - 1
      have hg : actVal σ g ≤ W - 1 := hv g List.mem_cons_self
      have hWpos : 0 < W := by omega
      have hpow : 0 < W ^ e := Nat.pow_pos hWpos
      cases rest with
      | nil =>
          have h1 : actVal σ g * W ^ e ≤ (W - 1) * W ^ e :=
            Nat.mul_le_mul_right _ hg
          have h2 : (W - 1) * W ^ e + 1 ≤ W ^ (e + 1) := by
            have hmul : (W - 1) * W ^ e + W ^ e = W ^ (e + 1) := by
              obtain ⟨w, rfl⟩ : ∃ w, W = w + 1 := ⟨W - 1, by omega⟩
              simp only [Nat.add_sub_cancel]
              rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_comm ((w + 1) ^ e) w]
            omega
          show actVal σ g * W ^ e + 0 ≤ W ^ (e + 1) - 1
          omega
      | cons g2 rest2 =>
          have he : 1 ≤ e := by
            simp only [List.length_cons] at hlen
            omega
          have hrest : measAux W σ (e - 1) (g2 :: rest2) ≤ W ^ (e - 1 + 1) - 1 := by
            refine ih (e - 1) (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg')) ?_
            simp only [List.length_cons] at hlen ⊢
            omega
          have hee : e - 1 + 1 = e := by omega
          rw [hee] at hrest
          have h1 : actVal σ g * W ^ e ≤ (W - 1) * W ^ e :=
            Nat.mul_le_mul_right _ hg
          have h2 : (W - 1) * W ^ e + W ^ e = W ^ (e + 1) := by
            obtain ⟨w, rfl⟩ : ∃ w, W = w + 1 := ⟨W - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_comm ((w + 1) ^ e) w]
          omega

/-! ## Chain length bound via activation depths -/

/-- Along a chain, length plus the first activation's depth is capped:
depths increment (`DepthLink`) and stay ≤ `maxChainDepth`. -/
theorem chain_length_depth {σ : MachineState} (hwf : Wf σ) (hdl : DepthLink σ) :
    ∀ {x : DomainId} {l : List GateId} {h : DomainId}, ChainFrom σ x l h →
    ∀ {g₀ : GateId} {rest : List GateId}, l = g₀ :: rest →
    ∀ a₀, (σ.gates g₀).act = some a₀ → l.length + a₀.depth ≤ maxChainDepth + 1 := by
  intro x l h hcf
  induction hcf with
  | top _ => intro g₀ rest hl; exact absurd hl (by simp)
  | link hb hrest ih =>
      rename_i x' g rest' h'
      intro g₀ rest hl a₀ ha₀
      injection hl with hg hrest'
      subst hg
      subst hrest'
      cases hrest with
      | top _ =>
          have := (hwf.gate_serving g a₀ ha₀).2.2.2
          simp only [List.length_cons, List.length_nil]
          omega
      | link hb2 hrest2 =>
          rename_i g₁ rest₁
          obtain ⟨a₁, ha₁, hc₁⟩ := hwf.blocked_gate _ g₁ hb2
          have hserv : (σ.doms (gateCallee σ g)).serving = some g :=
            (hwf.gate_serving g a₀ ha₀).1
          have hdep : a₁.depth = a₀.depth + 1 :=
            (hdl g₁ a₁ ha₁).2 g a₀ (by rw [hc₁]; exact hserv) ha₀
          have := ih rfl a₁ ha₁
          simp only [List.length_cons] at this ⊢
          omega

/-- A nonempty chain has length ≤ `maxChainDepth`. -/
theorem chain_length_le {σ : MachineState} (hwf : Wf σ) (hdl : DepthLink σ)
    {x : DomainId} {l : List GateId} {h : DomainId} (hcf : ChainFrom σ x l h) :
    l.length ≤ maxChainDepth := by
  cases l with
  | nil => exact Nat.zero_le _
  | cons g₀ rest =>
      cases hcf with
      | link hb hrest =>
          obtain ⟨a₀, ha₀, _⟩ := hwf.blocked_gate _ g₀ hb
          have hd1 : 1 ≤ a₀.depth := (hwf.gate_serving g₀ a₀ ha₀).2.2.1
          have := chain_length_depth hwf hdl (.link hb hrest) rfl a₀ ha₀
          simp only [List.length_cons] at this ⊢
          omega

/-! ## Chain surgery: break and extend -/

/-- If the only run changes are at a domain `b` that is now running, the
chain either survives whole or truncates exactly at `b`'s first occurrence
(a *pop*). -/
theorem ChainFrom.break {σ σ' : MachineState} {x : DomainId} {l : List GateId}
    {h : DomainId} (hcf : ChainFrom σ x l h)
    (hconf : ∀ g ∈ l, gateCallee σ' g = gateCallee σ g)
    (b : DomainId) (hbrun : (σ'.doms b).run = .running)
    (hrun : ∀ y ∈ chainMembers σ x l, y ≠ b → (σ'.doms y).run = (σ.doms y).run) :
    ChainFrom σ' x l h ∨
    ∃ l₁ g0 l₂, l = l₁ ++ g0 :: l₂ ∧ ChainFrom σ' x l₁ b := by
  induction hcf with
  | top hr =>
      rename_i x'
      by_cases hxb : x' = b
      · subst hxb
        exact .inl (.top hbrun)
      · refine .inl (.top ?_)
        rw [hrun x' List.mem_cons_self hxb]
        exact hr
  | link hb2 hrest ih =>
      rename_i x' g rest h'
      by_cases hxb : x' = b
      · subst hxb
        exact .inr ⟨[], g, rest, rfl, .top hbrun⟩
      · have hbx : (σ'.doms x').run = .blocked g := by
          rw [hrun x' List.mem_cons_self hxb]
          exact hb2
        have hsub : ∀ y ∈ chainMembers σ (gateCallee σ g) rest, y ≠ b →
            (σ'.doms y).run = (σ.doms y).run := by
          intro y hy hyb
          refine hrun y ?_ hyb
          unfold chainMembers at hy ⊢
          simp only [List.map_cons]
          rcases List.mem_cons.mp hy with h1 | h1
          · exact List.mem_cons_of_mem _ (h1 ▸ List.mem_cons_self)
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)
        rcases ih (fun g' hg' => hconf g' (List.mem_cons_of_mem _ hg')) hsub with
          h1 | ⟨l₁, g0, l₂, hl, hcf'⟩
        · refine .inl (.link hbx ?_)
          rw [hconf g List.mem_cons_self]
          exact h1
        · refine .inr ⟨g :: l₁, g0, l₂, by rw [hl]; rfl, .link hbx ?_⟩
          rw [hconf g List.mem_cons_self]
          exact hcf'

/-- If the only run change is the head blocking on a fresh gate whose callee
now runs, the chain extends by that gate (a *push*). -/
theorem ChainFrom.extend {σ σ' : MachineState} {x : DomainId} {l : List GateId}
    {h : DomainId} (hcf : ChainFrom σ x l h)
    (hconf : ∀ g ∈ l, gateCallee σ' g = gateCallee σ g)
    {gnew : GateId} (hbrun : (σ'.doms h).run = .blocked gnew)
    (hnewrun : (σ'.doms (gateCallee σ' gnew)).run = .running)
    (hrun : ∀ y ∈ chainMembers σ x l, y ≠ h → (σ'.doms y).run = (σ.doms y).run) :
    ChainFrom σ' x (l ++ [gnew]) (gateCallee σ' gnew) := by
  induction hcf with
  | top hr =>
      exact .link hbrun (.top hnewrun)
  | link hb2 hrest ih =>
      rename_i x' g rest h'
      have hxh : x' ≠ h' := by
        intro hE
        have htop := hrest.top_running
        rw [← hE] at htop
        rw [htop] at hb2
        exact absurd hb2 (by simp)
      refine .link ?_ ?_
      · rw [hrun x' List.mem_cons_self hxh]
        exact hb2
      · rw [hconf g List.mem_cons_self]
        refine ih (fun g' hg' => hconf g' (List.mem_cons_of_mem _ hg')) hbrun ?_
        intro y hy hyh
        refine hrun y ?_ hyh
        unfold chainMembers at hy ⊢
        simp only [List.map_cons]
        rcases List.mem_cons.mp hy with h1 | h1
        · exact List.mem_cons_of_mem _ (h1 ▸ List.mem_cons_self)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1)

/-! ## The measure as a state function -/

/-- The chain gate list, as a fuel-bounded function (agrees with
`ChainFrom` whenever the chain fits the fuel, `chainGatesF_eq`). -/
def chainGatesF (σ : MachineState) : Nat → DomainId → List GateId
  | 0, _ => []
  | fuel + 1, x =>
      match (σ.doms x).run with
      | .blocked gx => gx :: chainGatesF σ fuel (gateCallee σ gx)
      | _ => []

theorem chainGatesF_eq {σ : MachineState} {x : DomainId} {l : List GateId}
    {h : DomainId} (hcf : ChainFrom σ x l h) :
    ∀ fuel, l.length ≤ fuel → chainGatesF σ fuel x = l := by
  induction hcf with
  | top hrun =>
      intro fuel _
      cases fuel with
      | zero => rfl
      | succ f =>
          show (match (σ.doms _).run with
            | .blocked gx => gx :: chainGatesF σ f (gateCallee σ gx)
            | _ => ([] : List GateId)) = []
          rw [hrun]
  | link hb hrest ih =>
      rename_i x' g rest h'
      intro fuel hlen
      cases fuel with
      | zero => simp at hlen
      | succ f =>
          show (match (σ.doms x').run with
            | .blocked gx => gx :: chainGatesF σ f (gateCallee σ gx)
            | _ => ([] : List GateId)) = g :: rest
          rw [hb]
          show g :: chainGatesF σ f (gateCallee σ g) = g :: rest
          rw [ih f (by simpa using Nat.le_of_succ_le_succ hlen)]

/-- The T6 radix base: one more than any digit. -/
def chainW (m : Manifest) : Nat := maxDonationBound m + 2

theorem chainW_ge_two (m : Manifest) : 2 ≤ chainW m := by
  unfold chainW
  omega

/-- **The T6 progress measure** of a blocked domain's chain. -/
def chainMeasure (m : Manifest) (σ : MachineState) (d : DomainId) : Nat :=
  measAux (chainW m) σ (maxChainDepth - 1) (chainGatesF σ maxChainDepth d)

/-- Compute the measure from the relational chain. -/
theorem chainMeasure_of_chain {m : Manifest} {σ : MachineState} {d : DomainId}
    {l : List GateId} {h : DomainId} (hcf : ChainFrom σ d l h)
    (hlen : l.length ≤ maxChainDepth) :
    chainMeasure m σ d = measAux (chainW m) σ (maxChainDepth - 1) l := by
  unfold chainMeasure
  rw [chainGatesF_eq hcf maxChainDepth hlen]

/-- The measure is bounded by the radix order type. -/
theorem chainMeasure_lt (m : Manifest) {σ : MachineState} (hwf : Wf σ)
    (hdl : DepthLink σ) (hdon : DonatedLe m σ) {d : DomainId} {l : List GateId}
    {h : DomainId} (hcf : ChainFrom σ d l h) :
    chainMeasure m σ d < chainW m ^ maxChainDepth := by
  have hlen : l.length ≤ maxChainDepth := chain_length_le hwf hdl hcf
  rw [chainMeasure_of_chain hcf hlen]
  have hb := measAux_bound (σ := σ) (chainW_ge_two m) l (maxChainDepth - 1)
    (fun g _ => by
      have := actVal_le_of_donatedLe hdon g
      unfold chainW
      omega)
    (by omega)
  have hpow : 0 < chainW m ^ maxChainDepth :=
    Nat.pow_pos (by have := chainW_ge_two m; omega)
  have he : maxChainDepth - 1 + 1 = maxChainDepth := by decide
  rw [he] at hb
  omega

/-- The measure of a *blocked* domain is positive: the first digit is a live
activation. -/
theorem chainMeasure_pos (m : Manifest) {σ : MachineState} (hwf : Wf σ)
    {d : DomainId} {l : List GateId} {h : DomainId} (hcf : ChainFrom σ d l h)
    (hlen : l.length ≤ maxChainDepth) {g : GateId}
    (hb : (σ.doms d).run = .blocked g) :
    1 ≤ chainMeasure m σ d := by
  rw [chainMeasure_of_chain hcf hlen]
  cases hcf with
  | top hrun => rw [hrun] at hb; exact absurd hb (by simp)
  | link hb2 hrest =>
      rename_i g' rest'
      obtain ⟨a, ha, _⟩ := hwf.blocked_gate d g' hb2
      show 1 ≤ actVal σ g' * chainW m ^ (maxChainDepth - 1) +
        measAux (chainW m) σ (maxChainDepth - 1 - 1) rest'
      have h1 : 1 * 1 ≤ actVal σ g' * chainW m ^ (maxChainDepth - 1) :=
        Nat.mul_le_mul (actVal_pos ha)
          (Nat.pow_pos (by have := chainW_ge_two m; omega))
      omega

end Machines.Lnp64u
