-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Netlist.Cells

/-!
# The encoder, proved (D32) — part 1: the gate layer

`Loom/Netlist/Cells.lean` builds CNF in the `M` monad out of five
primitives (`fresh`, `addCl`, `mkAnd`, `mkXor`, `mkIte` and the two list
reductions). This file gives that layer a specification and proves it:

* `Enc n₀ act val` — "running `act` from a well-formed state produces bits
  that denote `val`". It has **both** directions of the Tseitin argument:
  - *backward* (`den f a = val f` for every `f` satisfying the produced
    clauses): what makes an UNSAT verdict mean something;
  - *forward* (every model of the state so far extends to a model of the
    new clauses in which the bits denote `val`): what makes a SAT verdict —
    a countermodel — mean something.

Everything is stated over the `Bit`/`Var` vocabulary of `Loom.Dp.Cnf`, so
the same lemmas serve the µVerilog side (`Loom/Netlist/Miter.lean`) and any
other client of these gates.

Nothing here is executed: these are proofs about the encoder the tool runs,
not a second encoder.
-/

namespace Loom.Netlist

open Loom.Dp.Cnf

/-! ## Well-formedness: which variables a bit may mention -/

/-- A variable is well-formed below `n` when, if it is an auxiliary Tseitin
variable, it was already allocated (`id < n`). Named (register/input/`rst`)
variables are always well-formed: they are the free variables of the miter. -/
def VarWF (n : Nat) : Var → Prop
  | .reg _ _ _ _ => True
  | .aux i => i < n

/-- A bit mentions only variables well-formed below `n`. -/
def BitWF (n : Nat) : Bit → Prop
  | .const _ => True
  | .lit v _ => VarWF n v

/-- Every literal of the clause is well-formed below `n`. -/
def ClWF (n : Nat) (cl : BClause) : Prop := ∀ b ∈ cl, BitWF n b

/-- Encoder states are well formed: every accumulated clause mentions only
already-allocated auxiliary variables. -/
def StWF (s : St) : Prop := ∀ cl ∈ s.clauses.toList, ClWF s.next cl

/-- `f` satisfies every clause accumulated in `s`. -/
def SatSt (f : Var → Bool) (s : St) : Prop :=
  ∀ cl ∈ s.clauses.toList, ∃ b ∈ cl, b.denote f = true

/-- Two assignments agree on everything well-formed below `n` — i.e. they
differ only on auxiliary variables not yet allocated. -/
def Agree (n : Nat) (f g : Var → Bool) : Prop := ∀ v, VarWF n v → f v = g v

theorem VarWF.mono {m n : Nat} {v : Var} (h : m ≤ n) : VarWF m v → VarWF n v := by
  cases v <;> simp [VarWF] <;> omega

theorem BitWF.mono {m n : Nat} {b : Bit} (h : m ≤ n) : BitWF m b → BitWF n b := by
  cases b <;> simp [BitWF] <;> exact VarWF.mono h

theorem ClWF.mono {m n : Nat} {cl : BClause} (h : m ≤ n) (hc : ClWF m cl) : ClWF n cl :=
  fun b hb => BitWF.mono h (hc b hb)

theorem BitWF.not {n : Nat} {b : Bit} (h : BitWF n b) : BitWF n b.not := by
  cases b <;> simpa [BitWF, Bit.not] using h

theorem Agree.refl (n : Nat) (f : Var → Bool) : Agree n f f := fun _ _ => rfl

theorem Agree.antitone {m n : Nat} {f g : Var → Bool} (h : m ≤ n) (ha : Agree n f g) :
    Agree m f g := fun v hv => ha v (VarWF.mono h hv)

theorem Agree.trans {m n : Nat} {f g h : Var → Bool} (h₁ : Agree n f g) (h₂ : Agree m g h)
    (hnm : n ≤ m) : Agree n f h := fun v hv => (h₁ v hv).trans (h₂ v (VarWF.mono hnm hv))

/-- Well-formed bits denote the same value under agreeing assignments. -/
theorem BitWF.denote_congr {n : Nat} {b : Bit} {f g : Var → Bool}
    (hb : BitWF n b) (ha : Agree n f g) : b.denote f = b.denote g := by
  cases b with
  | const c => rfl
  | lit v p => simp [Bit.denote, ha v hb]

theorem ClWF.sat_congr {n : Nat} {cl : BClause} {f g : Var → Bool}
    (hc : ClWF n cl) (ha : Agree n f g) (h : ∃ b ∈ cl, b.denote f = true) :
    ∃ b ∈ cl, b.denote g = true := by
  obtain ⟨b, hb, hbv⟩ := h
  exact ⟨b, hb, by rw [← (hc b hb).denote_congr ha]; exact hbv⟩

theorem SatSt.congr {s : St} {f g : Var → Bool} (hw : StWF s) (ha : Agree s.next f g)
    (h : SatSt f s) : SatSt g s :=
  fun cl hcl => (hw cl hcl).sat_congr ha (h cl hcl)

/-- Satisfaction is inherited by prefixes of the clause list. -/
theorem SatSt.of_prefix {s s' : St} {f : Var → Bool}
    (hp : ∃ new, s'.clauses.toList = s.clauses.toList ++ new) (h : SatSt f s') : SatSt f s := by
  obtain ⟨new, hnew⟩ := hp
  intro cl hcl
  exact h cl (by rw [hnew]; exact List.mem_append_left _ hcl)

/-! ## Denotation of encoder results -/

/-- What an encoder result of type `α` denotes, and when it is well formed.
Instantiated at `Bit` (one bit) and `Array Bit` (a bit vector). -/
class Deno (α : Type) (β : outParam Type) where
  wf : Nat → α → Prop
  den : (Var → Bool) → α → β
  den_congr : ∀ {n : Nat} {f g : Var → Bool} {a : α}, wf n a → Agree n f g → den f a = den g a
  wf_mono : ∀ {m n : Nat} {a : α}, m ≤ n → wf m a → wf n a

instance : Deno Bit Bool where
  wf := BitWF
  den := fun f b => b.denote f
  den_congr := fun hb ha => hb.denote_congr ha
  wf_mono := fun h hb => BitWF.mono h hb

instance : Deno (Array Bit) (Array Bool) where
  wf := fun n a => ∀ b ∈ a, BitWF n b
  den := fun f a => a.map (·.denote f)
  den_congr := by
    intro n f g a hwf ha
    apply Array.ext
    · simp
    · intro i h₁ h₂
      simp only [Array.getElem_map]
      exact (hwf _ (Array.getElem_mem (by simpa using h₁))).denote_congr ha
  wf_mono := fun h hwf b hb => BitWF.mono h (hwf b hb)

/-- A semantic value depends only on what is well formed below `n`. -/
def Stable {β : Type} (n : Nat) (val : (Var → Bool) → β) : Prop :=
  ∀ f g, Agree n f g → val f = val g

theorem Stable.mono {β : Type} {m n : Nat} {val : (Var → Bool) → β} (h : m ≤ n)
    (hs : Stable m val) : Stable n val := fun f g ha => hs f g (ha.antitone h)

/-! ## The encoder specification -/

/-- `Enc n₀ act val`: `act` is a **faithful** encoder of the value `val`.

Run from any well-formed state whose counter is at least `n₀` (the point
below which `act`'s input bits and `val` live), `act`
* leaves the state well formed and only appends clauses;
* returns a result whose bits are well formed;
* *backward*: under any assignment satisfying the clauses it produced, the
  result denotes `val`;
* *forward*: any assignment satisfying the clauses so far extends — on
  freshly allocated auxiliary variables only — to one that satisfies the new
  clauses and in which the result denotes `val`.

The two last clauses are the two directions of `encode_sound`. -/
def Enc {α β : Type} [Deno α β] (n₀ : Nat) (act : M α) (val : (Var → Bool) → β) : Prop :=
  ∀ (s : St) (a : α) (s' : St), StWF s → n₀ ≤ s.next → M.run act s = (.ok a, s') →
    StWF s' ∧ s.next ≤ s'.next ∧ Deno.wf s'.next a ∧
    (∃ new, s'.clauses.toList = s.clauses.toList ++ new) ∧
    (∀ f, SatSt f s' → Deno.den f a = val f) ∧
    (∀ f, SatSt f s → ∃ g, Agree s.next f g ∧ SatSt g s' ∧ Deno.den g a = val g)

/-! ## Running the monad -/

theorem run_bind {α β : Type} (m : M α) (k : α → M β) (s : St) :
    M.run (m >>= k) s = (match M.run m s with
      | (.ok a, s') => M.run (k a) s'
      | (.error e, s') => (.error e, s')) := by
  cases h : M.run m s with
  | mk a s' =>
    cases a with
    | error e =>
      simp only [M.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
      simp_all [M.run, StateT.run]
      rfl
    | ok a =>
      simp only [M.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind]
      simp_all [M.run, StateT.run]

theorem run_pure {α : Type} (a : α) (s : St) : M.run (pure a : M α) s = (.ok a, s) := rfl

theorem run_throw {α : Type} (e : String) (s : St) : M.run (throw e : M α) s = (.error e, s) := rfl

theorem run_addCl (c : BClause) (s : St) :
    M.run (addCl c) s = (.ok (), { s with clauses := s.clauses.push c }) := rfl

theorem run_fresh (s : St) :
    M.run fresh s = (.ok (Bit.lit (.aux s.next) true), { s with next := s.next + 1 }) := rfl

/-! ## Structural rules -/

theorem Enc.pure {α β : Type} [Deno α β] {n₀ : Nat} {a : α} {val : (Var → Bool) → β}
    (hwf : Deno.wf n₀ a) (hval : ∀ f, Deno.den f a = val f) :
    Enc n₀ (Pure.pure a) val := by
  intro s a' s' hs hn hrun
  rw [run_pure] at hrun
  cases hrun
  exact ⟨hs, Nat.le_refl _, Deno.wf_mono hn hwf, ⟨[], by simp⟩,
    fun f _ => hval f, fun f hf => ⟨f, Agree.refl _ _, hf, hval f⟩⟩

/-- Sequential composition. `valB` may depend on the value the first action
denotes — which is how a gate is specified in terms of its inputs. `P` is
any *functional* property of the first action's result (e.g. its width),
available to the continuation. -/
theorem Enc.bind' {α β α' β' : Type} [Deno α β] [Deno α' β'] {n₀ : Nat}
    {m : M α} {k : α → M α'} {valA : (Var → Bool) → β} {valB : β → (Var → Bool) → β'}
    {P : α → Prop}
    (hA : Stable n₀ valA)
    (hP : ∀ s a s', M.run m s = (.ok a, s') → P a)
    (hm : Enc n₀ m valA)
    (hk : ∀ (a : α) (n : Nat), n₀ ≤ n → Deno.wf n a → P a →
      Enc n (k a) (fun f => valB (Deno.den f a) f)) :
    Enc n₀ (m >>= k) (fun f => valB (valA f) f) := by
  intro s c s' hs hn hrun
  rw [run_bind] at hrun
  revert hrun
  cases hm' : M.run m s with
  | mk r s₁ =>
    cases r with
    | error e => intro h; simp at h
    | ok a =>
      intro hrun
      simp only at hrun
      obtain ⟨hs₁, hn₁, hwa, hpre₁, hback₁, hfwd₁⟩ := hm s a s₁ hs hn hm'
      obtain ⟨hs₂, hn₂, hwc, hpre₂, hback₂, hfwd₂⟩ :=
        hk a s₁.next (Nat.le_trans hn hn₁) hwa (hP s a s₁ hm') s₁ c s' hs₁ (Nat.le_refl _) hrun
      refine ⟨hs₂, Nat.le_trans hn₁ hn₂, hwc, ?_, ?_, ?_⟩
      · obtain ⟨n1, h1⟩ := hpre₁; obtain ⟨n2, h2⟩ := hpre₂
        exact ⟨n1 ++ n2, by rw [h2, h1, List.append_assoc]⟩
      · intro f hf
        have hf₁ : SatSt f s₁ := SatSt.of_prefix hpre₂ hf
        refine (hback₂ f hf).trans ?_
        show valB (Deno.den f a) f = valB (valA f) f
        rw [hback₁ f hf₁]
      · intro f hf
        obtain ⟨g₁, hag₁, hsg₁, hdg₁⟩ := hfwd₁ f hf
        obtain ⟨g₂, hag₂, hsg₂, hdg₂⟩ := hfwd₂ g₁ hsg₁
        refine ⟨g₂, hag₁.trans hag₂ hn₁, hsg₂, ?_⟩
        have hden : Deno.den g₂ a = Deno.den g₁ a := (Deno.den_congr hwa hag₂).symm
        refine hdg₂.trans ?_
        show valB (Deno.den g₂ a) g₂ = valB (valA g₂) g₂
        rw [hden, hdg₁]
        exact congrArg (fun b => valB b g₂) (hA g₁ g₂ (hag₂.antitone (Nat.le_trans hn hn₁)))

/-! ## The gate rule

Every gate in `Cells.lean` is `mkGate cls`: allocate a fresh output
variable and add the clauses that define it. `Enc_mkGate` discharges the
freshness bookkeeping once and for all; each gate then only has to say what
its clauses force (`hforce`) and that they are satisfied by the intended
value (`hmodel`) — two finite Boolean case analyses. -/

theorem run_addCls (L : List BClause) (s : St) :
    M.run (addCls L) s = (.ok (), { s with clauses := s.clauses ++ L.toArray }) := by
  induction L generalizing s with
  | nil => simp [addCls, run_pure]
  | cons c cs ih =>
    show M.run (addCl c >>= fun _ => addCls cs) s = _
    rw [run_bind, run_addCl]
    simp only []
    rw [ih]
    simp

theorem Enc_mkGate {n₀ : Nat} (val : (Var → Bool) → Bool) (cls : Bit → List BClause)
    (hstable : Stable n₀ val)
    (hwf : ∀ (o : Bit) (n : Nat), n₀ ≤ n → BitWF n o → ∀ cl ∈ cls o, ClWF n cl)
    (hforce : ∀ (f : Var → Bool) (o : Bit),
        (∀ cl ∈ cls o, ∃ b ∈ cl, b.denote f = true) → o.denote f = val f)
    (hmodel : ∀ (f : Var → Bool) (o : Bit),
        o.denote f = val f → ∀ cl ∈ cls o, ∃ b ∈ cl, b.denote f = true) :
    Enc n₀ (mkGate cls) val := by
  intro s a s' hs hn hrun
  -- Run the three steps.
  have hrun' : M.run (mkGate cls) s =
      (.ok (Bit.lit (.aux s.next) true),
        (⟨s.next + 1, s.clauses ++ (cls (.lit (.aux s.next) true)).toArray, s.memo, s.amemo⟩ : St)) := by
    show M.run (fresh >>= fun o => addCls (cls o) >>= fun _ => Pure.pure o) s = _
    rw [run_bind, run_fresh]
    simp only []
    rw [run_bind, run_addCls]
    simp only []
    rw [run_pure]
  rw [hrun'] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (by simpa using hrun : _ ∧ _)
  set o : Bit := Bit.lit (.aux s.next) true with ho
  have hwfo : BitWF (s.next + 1) o := by simp [ho, BitWF, VarWF]
  have hclauses : ((⟨s.next + 1, s.clauses ++ (cls o).toArray, s.memo, s.amemo⟩ : St)).clauses.toList
      = s.clauses.toList ++ cls o := by simp
  have hnewWF : ∀ cl ∈ cls o, ClWF (s.next + 1) cl :=
    hwf o (s.next + 1) (Nat.le_trans hn (Nat.le_succ _)) hwfo
  refine ⟨?_, Nat.le_succ _, hwfo, ⟨cls o, hclauses⟩, ?_, ?_⟩
  · intro cl hcl
    rw [hclauses] at hcl
    rcases List.mem_append.mp hcl with h | h
    · exact ClWF.mono (Nat.le_succ _) (hs cl h)
    · exact hnewWF cl h
  · intro f hf
    refine hforce f o (fun cl hcl => hf cl ?_)
    rw [hclauses]; exact List.mem_append_right _ hcl
  · intro f hf
    set g : Var → Bool := fun v => if v = .aux s.next then val f else f v with hg
    have hag : Agree s.next f g := by
      intro v hv
      have hne : v ≠ .aux s.next := by
        cases v with
        | reg _ _ _ _ => simp
        | aux i => simp only [ne_eq, Var.aux.injEq]; simp [VarWF] at hv; omega
      simp [hg, hne]
    have hvalg : val g = val f := (hstable f g (hag.antitone hn)).symm
    have hgo : g (.aux s.next) = val f := by simp [hg]
    have hden : Bit.denote g o = val g := by rw [hvalg, ho]; simp [Bit.denote, hgo]
    refine ⟨g, hag, ?_, hden⟩
    intro cl hcl
    rw [hclauses] at hcl
    rcases List.mem_append.mp hcl with h | h
    · exact (hs cl h).sat_congr hag (hf cl h)
    · exact hmodel g o hden cl h

/-! ## Denotation simp lemmas -/

@[simp] theorem den_bit (f : Var → Bool) (b : Bit) : (Deno.den f b : Bool) = b.denote f := rfl
@[simp] theorem wf_bit (n : Nat) (b : Bit) : (Deno.wf n b : Prop) = BitWF n b := rfl
@[simp] theorem den_bits (f : Var → Bool) (a : Array Bit) :
    (Deno.den f a : Array Bool) = a.map (·.denote f) := rfl
@[simp] theorem wf_bits (n : Nat) (a : Array Bit) :
    (Deno.wf n a : Prop) = ∀ b ∈ a, BitWF n b := rfl

theorem Enc.bind {α β α' β' : Type} [Deno α β] [Deno α' β'] {n₀ : Nat}
    {m : M α} {k : α → M α'} {valA : (Var → Bool) → β} {valB : β → (Var → Bool) → β'}
    (hA : Stable n₀ valA)
    (hm : Enc n₀ m valA)
    (hk : ∀ (a : α) (n : Nat), n₀ ≤ n → Deno.wf n a →
      Enc n (k a) (fun f => valB (Deno.den f a) f)) :
    Enc n₀ (m >>= k) (fun f => valB (valA f) f) :=
  Enc.bind' (P := fun _ => True) hA (fun _ _ _ _ => trivial) hm
    (fun a n hn hwa _ => hk a n hn hwa)

/-! ## The gates of `Cells.lean` -/

theorem Stable.and {n₀ : Nat} {x y : Bit} (hx : BitWF n₀ x) (hy : BitWF n₀ y) :
    Stable n₀ (fun f => x.denote f && y.denote f) := by
  intro f g ha
  show (Bit.denote f x && Bit.denote f y) = (Bit.denote g x && Bit.denote g y)
  rw [hx.denote_congr ha, hy.denote_congr ha]

/-- The three defining clauses of an AND gate force its output. -/
theorem Enc_mkAnd {n₀ : Nat} {x y : Bit} (hx : BitWF n₀ x) (hy : BitWF n₀ y) :
    Enc n₀ (mkAnd x y) (fun f => x.denote f && y.denote f) := by
  have hgate : Enc n₀ (mkGate (fun o => [[o.not, x], [o.not, y], [o, x.not, y.not]]))
      (fun f => x.denote f && y.denote f) := by
    refine Enc_mkGate _ _ (Stable.and hx hy) ?_ ?_ ?_
    · intro o n hn hwo cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl <;> intro b hb <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;>
        rcases hb with rfl | rfl | rfl <;>
        first
          | exact hwo.not | exact hwo
          | exact (BitWF.mono hn hx) | exact (BitWF.mono hn hy)
          | exact (BitWF.mono hn hx).not | exact (BitWF.mono hn hy).not
    · intro f o h
      have h1 := h [o.not, x] (by simp)
      have h2 := h [o.not, y] (by simp)
      have h3 := h [o, x.not, y.not] (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left, Bit.denote_not, Bool.not_eq_true'] at h1 h2 h3 ⊢
      cases ho : o.denote f <;> cases hx' : x.denote f <;> cases hy' : y.denote f <;> simp_all
    · intro f o hden cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      simp only at hden
      rcases hcl with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
          exists_eq_left, Bit.denote_not, Bool.not_eq_true'] <;>
        cases hx' : x.denote f <;> cases hy' : y.denote f <;> simp_all
  cases x with
  | const bx =>
    cases bx with
    | false => exact Enc.pure (by trivial) (by simp [Bit.denote])
    | true =>
      cases y with
      | const by' =>
        cases by' with
        | false => exact Enc.pure (by trivial) (by simp [Bit.denote])
        | true => exact Enc.pure (by trivial) (by simp [Bit.denote])
      | lit vy py => exact Enc.pure hy (by simp [Bit.denote])
  | lit vx px =>
    cases y with
    | const by' =>
      cases by' with
      | false => exact Enc.pure (by trivial) (by simp [Bit.denote])
      | true => exact Enc.pure hx (by simp [Bit.denote])
    | lit vy py =>
      show Enc n₀ (if (Bit.lit vx px) == (Bit.lit vy py) then _ else _) _
      split
      · rename_i heq
        have h : Bit.lit vx px = Bit.lit vy py := by simpa using heq
        rw [h]
        refine Enc.pure hy (fun f => ?_)
        obtain ⟨rfl, rfl⟩ : vx = vy ∧ px = py := by simpa using h
        show Bit.denote f (Bit.lit vx px)
            = (Bit.denote f (Bit.lit vx px) && Bit.denote f (Bit.lit vx px))
        simp
      · split
        · rename_i heq
          have h : Bit.lit vx px = (Bit.lit vy py).not := by simpa using heq
          refine Enc.pure (by trivial) (fun f => ?_)
          show Bit.denote f (.const false)
              = (Bit.denote f (Bit.lit vx px) && Bit.denote f (Bit.lit vy py))
          rw [h]
          cases hb : Bit.denote f (Bit.lit vy py) <;> simp [Bit.denote_not, hb]
        · exact hgate


theorem Enc.mono {α β : Type} [Deno α β] {m n : Nat} {act : M α} {val : (Var → Bool) → β}
    (h : m ≤ n) (he : Enc m act val) : Enc n act val :=
  fun s a s' hs hn hrun => he s a s' hs (Nat.le_trans h hn) hrun

theorem Enc.congr {α β : Type} [Deno α β] {n₀ : Nat} {act : M α} {val val' : (Var → Bool) → β}
    (h : ∀ f, val f = val' f) (he : Enc n₀ act val) : Enc n₀ act val' := by
  intro s a s' hs hn hrun
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := he s a s' hs hn hrun
  exact ⟨h1, h2, h3, h4, fun f hf => (h5 f hf).trans (h f),
    fun f hf => by obtain ⟨g, hg1, hg2, hg3⟩ := h6 f hf; exact ⟨g, hg1, hg2, hg3.trans (h g)⟩⟩

theorem Enc_mkOr {n₀ : Nat} {x y : Bit} (hx : BitWF n₀ x) (hy : BitWF n₀ y) :
    Enc n₀ (mkOr x y) (fun f => x.denote f || y.denote f) := by
  refine Enc.congr (α := Bit) (β := Bool) (val := fun f => !(x.not.denote f && y.not.denote f))
    (fun f => by simp) ?_
  refine Enc.bind (α := Bit) (α' := Bit) (valA := fun f => (x.not.denote f && y.not.denote f))
    (valB := fun b _ => !b) ?_ ?_ ?_
  · exact Stable.and hx.not hy.not
  · exact Enc_mkAnd hx.not hy.not
  · intro a n hn hwa
    exact Enc.pure hwa.not (fun f => by simp)

theorem Stable.bxor {n₀ : Nat} {x y : Bit} (hx : BitWF n₀ x) (hy : BitWF n₀ y) :
    Stable n₀ (fun f => (x.denote f) ^^ (y.denote f)) := by
  intro f g ha
  show (Bit.denote f x ^^ Bit.denote f y) = (Bit.denote g x ^^ Bit.denote g y)
  rw [hx.denote_congr ha, hy.denote_congr ha]

theorem Enc_mkXor {n₀ : Nat} {x y : Bit} (hx : BitWF n₀ x) (hy : BitWF n₀ y) :
    Enc n₀ (mkXor x y) (fun f => (x.denote f) ^^ (y.denote f)) := by
  have hgate : Enc n₀ (mkGate (fun o =>
      [[o.not, x, y], [o.not, x.not, y.not], [o, x.not, y], [o, x, y.not]]))
      (fun f => (x.denote f) ^^ (y.denote f)) := by
    refine Enc_mkGate _ _ (Stable.bxor hx hy) ?_ ?_ ?_
    · intro o n hn hwo cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl | rfl <;> intro b hb <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;>
        rcases hb with rfl | rfl | rfl <;>
        first
          | exact hwo.not | exact hwo
          | exact (BitWF.mono hn hx) | exact (BitWF.mono hn hy)
          | exact (BitWF.mono hn hx).not | exact (BitWF.mono hn hy).not
    · intro f o h
      have h1 := h [o.not, x, y] (by simp)
      have h2 := h [o.not, x.not, y.not] (by simp)
      have h3 := h [o, x.not, y] (by simp)
      have h4 := h [o, x, y.not] (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left, Bit.denote_not, Bool.not_eq_true'] at h1 h2 h3 h4 ⊢
      cases ho : o.denote f <;> cases hx' : x.denote f <;> cases hy' : y.denote f <;> simp_all
    · intro f o hden cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      simp only at hden
      rcases hcl with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
          exists_eq_left, Bit.denote_not, Bool.not_eq_true'] <;>
        cases hx' : x.denote f <;> cases hy' : y.denote f <;> simp_all
  cases x with
  | const bx =>
    cases y with
    | const by' => exact Enc.pure (by trivial) (fun f => by cases bx <;> cases by' <;> simp [Bit.denote])
    | lit vy py =>
      cases bx with
      | false => exact Enc.pure hy (fun f => by simp)
      | true => exact Enc.pure hy.not (fun f => by simp only [den_bit, Bit.denote_not]; simp)
  | lit vx px =>
    cases y with
    | const by' =>
      cases by' with
      | false => exact Enc.pure hx (fun f => by simp)
      | true => exact Enc.pure hx.not (fun f => by simp only [den_bit, Bit.denote_not]; simp)
    | lit vy py =>
      show Enc n₀ (if (Bit.lit vx px) == (Bit.lit vy py) then _ else _) _
      split
      · rename_i heq
        have h : Bit.lit vx px = Bit.lit vy py := by simpa using heq
        refine Enc.pure (by trivial) (fun f => ?_)
        obtain ⟨rfl, rfl⟩ : vx = vy ∧ px = py := by simpa using h
        show Bit.denote f (.const false)
            = ((Bit.denote f (Bit.lit vx px)) ^^ (Bit.denote f (Bit.lit vx px)))
        simp
      · split
        · rename_i heq
          have h : Bit.lit vx px = (Bit.lit vy py).not := by simpa using heq
          refine Enc.pure (by trivial) (fun f => ?_)
          show Bit.denote f (.const true)
              = ((Bit.denote f (Bit.lit vx px)) ^^ (Bit.denote f (Bit.lit vy py)))
          rw [h]
          cases hb : Bit.denote f (Bit.lit vy py) <;> simp [Bit.denote_not, hb]
        · exact hgate

theorem Stable.ite {n₀ : Nat} {c t e : Bit} (hc : BitWF n₀ c) (ht : BitWF n₀ t)
    (he : BitWF n₀ e) : Stable n₀ (fun f => cond (c.denote f) (t.denote f) (e.denote f)) := by
  intro f g ha
  show cond (Bit.denote f c) (Bit.denote f t) (Bit.denote f e)
      = cond (Bit.denote g c) (Bit.denote g t) (Bit.denote g e)
  rw [hc.denote_congr ha, ht.denote_congr ha, he.denote_congr ha]

theorem Enc_mkIte {n₀ : Nat} {c t e : Bit} (hc : BitWF n₀ c) (ht : BitWF n₀ t)
    (he : BitWF n₀ e) :
    Enc n₀ (mkIte c t e) (fun f => cond (c.denote f) (t.denote f) (e.denote f)) := by
  have hgate : Enc n₀ (mkGate (fun o =>
      [[o.not, c.not, t], [o, c.not, t.not], [o.not, c, e], [o, c, e.not]]))
      (fun f => cond (c.denote f) (t.denote f) (e.denote f)) := by
    refine Enc_mkGate _ _ (Stable.ite hc ht he) ?_ ?_ ?_
    · intro o n hn hwo cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl | rfl <;> intro b hb <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;>
        rcases hb with rfl | rfl | rfl <;>
        first
          | exact hwo.not | exact hwo
          | exact (BitWF.mono hn hc) | exact (BitWF.mono hn ht) | exact (BitWF.mono hn he)
          | exact (BitWF.mono hn hc).not | exact (BitWF.mono hn ht).not
          | exact (BitWF.mono hn he).not
    · intro f o h
      have h1 := h [o.not, c.not, t] (by simp)
      have h2 := h [o, c.not, t.not] (by simp)
      have h3 := h [o.not, c, e] (by simp)
      have h4 := h [o, c, e.not] (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left, Bit.denote_not, Bool.not_eq_true'] at h1 h2 h3 h4 ⊢
      cases ho : o.denote f <;> cases hc' : c.denote f <;> cases ht' : t.denote f <;>
        cases he' : e.denote f <;> simp_all
    · intro f o hden cl hcl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      simp only at hden
      rcases hcl with rfl | rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
          exists_eq_left, Bit.denote_not, Bool.not_eq_true'] <;>
        cases hc' : c.denote f <;> cases ht' : t.denote f <;> cases he' : e.denote f <;> simp_all
  cases c with
  | const bc =>
    cases bc with
    | true => exact Enc.pure ht (fun f => by simp [Bit.denote])
    | false => exact Enc.pure he (fun f => by simp [Bit.denote])
  | lit vc pc =>
    show Enc n₀ (if t == e then _ else _) _
    split
    · rename_i heq
      have h : t = e := by simpa using heq
      subst h
      refine Enc.pure ht (fun f => ?_)
      show Bit.denote f t = cond (Bit.denote f (Bit.lit vc pc)) (Bit.denote f t) (Bit.denote f t)
      cases Bit.denote f (Bit.lit vc pc) <;> simp
    · split
      · rename_i heq
        obtain ⟨h1, h2⟩ : t = Bit.const true ∧ e = Bit.const false := by
          simpa [Bool.and_eq_true] using heq
        subst h1; subst h2
        refine Enc.pure hc (fun f => ?_)
        show Bit.denote f (Bit.lit vc pc)
            = cond (Bit.denote f (Bit.lit vc pc)) (Bit.denote f (.const true))
                (Bit.denote f (.const false))
        cases hb : Bit.denote f (Bit.lit vc pc) <;> simp [Bit.denote, hb]
      · split
        · rename_i heq
          obtain ⟨h1, h2⟩ : t = Bit.const false ∧ e = Bit.const true := by
            simpa [Bool.and_eq_true] using heq
          subst h1; subst h2
          refine Enc.pure hc.not (fun f => ?_)
          simp only [den_bit, Bit.denote_not]
          cases hb : Bit.denote f (Bit.lit vc pc) <;> simp [hb]
        · exact hgate

/-! ## List and array reductions -/

theorem Stable.const {β : Type} {n₀ : Nat} (b : β) : Stable n₀ (fun _ => b) :=
  fun _ _ _ => rfl

theorem Stable.bit {n₀ : Nat} {x : Bit} (hx : BitWF n₀ x) : Stable n₀ (fun f => x.denote f) :=
  fun _ _ ha => hx.denote_congr ha

theorem Stable.allList {n₀ : Nat} : ∀ (l : List Bit), (∀ b ∈ l, BitWF n₀ b) →
    Stable n₀ (fun f => l.all (fun b => b.denote f))
  | [], _ => fun _ _ _ => rfl
  | b :: bs, h => by
      intro f g ha
      simp only [List.all_cons]
      rw [(h b (by simp)).denote_congr ha]
      exact congrArg _ (Stable.allList bs (fun x hx => h x (by simp [hx])) f g ha)

theorem Stable.anyList {n₀ : Nat} : ∀ (l : List Bit), (∀ b ∈ l, BitWF n₀ b) →
    Stable n₀ (fun f => l.any (fun b => b.denote f))
  | [], _ => fun _ _ _ => rfl
  | b :: bs, h => by
      intro f g ha
      simp only [List.any_cons]
      rw [(h b (by simp)).denote_congr ha]
      exact congrArg _ (Stable.anyList bs (fun x hx => h x (by simp [hx])) f g ha)

/-- The AND of a list of bits. -/
theorem Enc_mkAndList {n₀ : Nat} : ∀ (l : List Bit), (∀ b ∈ l, BitWF n₀ b) →
    Enc n₀ (mkAndList l) (fun f => l.all (fun b => b.denote f))
  | [], _ => Enc.pure (by trivial) (fun f => by simp)
  | b :: bs, h => by
    have hb : BitWF n₀ b := h b (by simp)
    have hbs : ∀ x ∈ bs, BitWF n₀ x := fun x hx => h x (by simp [hx])
    refine Enc.congr (α := Bit) (β := Bool)
      (val := fun f => b.denote f && (bs.all (fun x => x.denote f)))
      (fun f => by simp) ?_
    refine Enc.bind (α := Bit) (α' := Bit)
      (valA := fun f => bs.all (fun x => x.denote f))
      (valB := fun a f => b.denote f && a) (Stable.allList bs hbs) (Enc_mkAndList bs hbs) ?_
    · intro a n hn hwa
      exact Enc_mkAnd (BitWF.mono hn hb) hwa

/-- The OR of a list of bits. -/
theorem Enc_mkOrList {n₀ : Nat} : ∀ (l : List Bit), (∀ b ∈ l, BitWF n₀ b) →
    Enc n₀ (mkOrList l) (fun f => l.any (fun b => b.denote f))
  | [], _ => Enc.pure (by trivial) (fun f => by simp)
  | b :: bs, h => by
    have hb : BitWF n₀ b := h b (by simp)
    have hbs : ∀ x ∈ bs, BitWF n₀ x := fun x hx => h x (by simp [hx])
    refine Enc.congr (α := Bit) (β := Bool)
      (val := fun f => b.denote f || (bs.any (fun x => x.denote f)))
      (fun f => by simp) ?_
    refine Enc.bind (α := Bit) (α' := Bit)
      (valA := fun f => bs.any (fun x => x.denote f))
      (valB := fun a f => b.denote f || a) (Stable.anyList bs hbs) (Enc_mkOrList bs hbs) ?_
    · intro a n hn hwa
      exact Enc_mkOr (BitWF.mono hn hb) hwa

/-! ## Bit vectors: the array combinator

`buildM g k` is the shape every width-`k` blast has: encode bit `0`, then
bit `1`, … , in that order (the order the encoder's `for` loops used, hence
the same clauses in the same order). -/

instance {α β α' β' : Type} [Deno α β] [Deno α' β'] : Deno (α × α') (β × β') where
  wf := fun n p => Deno.wf n p.1 ∧ Deno.wf n p.2
  den := fun f p => (Deno.den f p.1, Deno.den f p.2)
  den_congr := fun h ha => by
    rw [Deno.den_congr h.1 ha, Deno.den_congr h.2 ha]
  wf_mono := fun h hw => ⟨Deno.wf_mono h hw.1, Deno.wf_mono h hw.2⟩

@[simp] theorem den_prod {α β α' β' : Type} [Deno α β] [Deno α' β'] (f : Var → Bool)
    (p : α × α') : (Deno.den f p : β × β') = (Deno.den f p.1, Deno.den f p.2) := rfl

@[simp] theorem wf_prod {α β α' β' : Type} [Deno α β] [Deno α' β'] (n : Nat) (p : α × α') :
    (Deno.wf n p : Prop) = (Deno.wf n p.1 ∧ Deno.wf n p.2) := rfl

/-- `#[← g 0, …, ← g (k-1)]`, evaluated left to right. -/
def buildM (g : Nat → M Bit) : Nat → M (Array Bit)
  | 0 => Pure.pure #[]
  | k + 1 => do
      let a ← buildM g k
      let b ← g k
      Pure.pure (a.push b)

theorem ofFn_succ {β : Type} {k : Nat} (v : Fin (k + 1) → β) :
    Array.ofFn v = (Array.ofFn (n := k) (fun i : Fin k => v i.castSucc)).push (v (Fin.last k)) := by
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp only [Array.size_ofFn] at h₁
    rcases Nat.lt_or_ge i k with h | h
    · rw [Array.getElem_ofFn, Array.getElem_push_lt (by simpa using h), Array.getElem_ofFn]
      rfl
    · have hik : i = k := by omega
      subst hik
      have hsz : (Array.ofFn (n := i) (fun j : Fin i => v j.castSucc)).size = i := by simp
      rw [Array.getElem_ofFn, Array.getElem_push]
      simp [hsz, Fin.last]

theorem Stable.ofFn {n₀ k : Nat} {val : Nat → (Var → Bool) → Bool}
    (hs : ∀ i, i < k → Stable n₀ (val i)) :
    Stable n₀ (fun f => Array.ofFn (n := k) fun i : Fin k => val i.val f) := by
  intro f g ha
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp only [Array.size_ofFn] at h₁
    rw [Array.getElem_ofFn, Array.getElem_ofFn]
    exact hs i h₁ f g ha

theorem Enc_buildM {n₀ : Nat} {g : Nat → M Bit} {val : Nat → (Var → Bool) → Bool} :
    ∀ (k : Nat), (∀ i, i < k → Enc n₀ (g i) (val i)) → (∀ i, i < k → Stable n₀ (val i)) →
      Enc n₀ (buildM g k) (fun f => Array.ofFn (n := k) fun i : Fin k => val i.val f)
  | 0, _, _ => Enc.pure (by simp) (fun f => by simp)
  | k + 1, hg, hs => by
    refine Enc.congr (α := Array Bit) (β := Array Bool)
      (val := fun f => (Array.ofFn (n := k) fun i : Fin k => val i.val f).push (val k f))
      (fun f => by rw [ofFn_succ]; rfl) ?_
    refine Enc.bind (α := Array Bit) (α' := Array Bit)
      (valA := fun f => Array.ofFn (n := k) fun i : Fin k => val i.val f)
      (valB := fun av f => av.push (val k f))
      (Stable.ofFn (fun i hi => hs i (by omega)))
      (Enc_buildM k (fun i hi => hg i (by omega)) (fun i hi => hs i (by omega))) ?_
    intro a n hn hwa
    refine Enc.bind (α := Bit) (α' := Array Bit) (valA := val k)
      (valB := fun b f => (a.map (·.denote f)).push b)
      (Stable.mono hn (hs k (by omega)))
      (Enc.mono hn (hg k (by omega))) ?_
    intro b n' hn' hwb
    refine Enc.pure ?_ (fun f => ?_)
    · intro c hc
      rcases Array.mem_push.mp hc with h | h
      · exact BitWF.mono hn' (hwa c h)
      · exact h ▸ hwb
    · simp

/-! ## Bit-vector encoders

`EncA n₀ w act val` = "`act` encodes the `w`-bit vector `val`": `Enc`, plus
the (purely functional) fact that it returns `w` bits, plus stability of the
value under the assignments that agree below `n₀`. -/

/-- The bits of a bit vector, LSB first — the shape a blaster returns. -/
def bitsOf {w : Nat} (v : BitVec w) : Array Bool :=
  Array.ofFn (n := w) fun i : Fin w => v.getLsbD i.val

@[simp] theorem bitsOf_size {w : Nat} (v : BitVec w) : (bitsOf v).size = w := by simp [bitsOf]

theorem bitsOf_getElem {w : Nat} (v : BitVec w) (i : Nat) (h : i < (bitsOf v).size) :
    (bitsOf v)[i] = v.getLsbD i := by
  simp only [bitsOf, Array.getElem_ofFn]

theorem getElem_bang {α : Type} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := by simp [getElem!_pos, h]

/-- `act` encodes the `w`-bit vector `val` (faithfully, both directions). -/
def EncA (n₀ w : Nat) (act : M (Array Bit)) (val : (Var → Bool) → BitVec w) : Prop :=
  (∀ s bits s', M.run act s = (.ok bits, s') → bits.size = w) ∧
  Stable n₀ val ∧
  Enc n₀ act (fun f => bitsOf (val f))

theorem Stable.bits {n₀ w : Nat} {val : (Var → Bool) → BitVec w} (h : Stable n₀ val) :
    Stable n₀ (fun f => bitsOf (val f)) := fun f g ha => congrArg bitsOf (h f g ha)

theorem EncA.congr {n₀ w : Nat} {act : M (Array Bit)} {val val' : (Var → Bool) → BitVec w}
    (h : ∀ f, val f = val' f) (he : EncA n₀ w act val) : EncA n₀ w act val' :=
  ⟨he.1, fun f g ha => by rw [← h, ← h]; exact he.2.1 f g ha,
    Enc.congr (fun f => by rw [h f]) he.2.2⟩

theorem EncA.mono {m n w : Nat} {act : M (Array Bit)} {val : (Var → Bool) → BitVec w}
    (h : m ≤ n) (he : EncA m w act val) : EncA n w act val :=
  ⟨he.1, Stable.mono h he.2.1, Enc.mono h he.2.2⟩

/-- Pointwise form of the denotation equation. -/
theorem den_pointwise {w : Nat} {x : Array Bit} {f : Var → Bool} {v : BitVec w}
    (hsz : x.size = w) (h : (Deno.den f x : Array Bool) = bitsOf v) (i : Nat) (hi : i < w) :
    (x[i]!).denote f = v.getLsbD i := by
  have hx : i < x.size := by omega
  have h2 : (x.map (·.denote f))[i]'(by simpa using hx) = (bitsOf v)[i]'(by simp; omega) := by
    simp only [← h]; rfl
  rw [Array.getElem_map] at h2
  rw [getElem_bang x i hx, h2, bitsOf_getElem]

theorem Stable.bv {n₀ w : Nat} {val : (Var → Bool) → BitVec w}
    (h : ∀ f g, Agree n₀ f g → ∀ i, i < w → (val f).getLsbD i = (val g).getLsbD i) :
    Stable n₀ val := by
  intro f g ha
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h f g ha i hi

/-- The `pure (Array.ofFn …)` shape: `lit` and `reg`. -/
theorem EncA_ofFn {n₀ w : Nat} (g : Fin w → Bit) (val : (Var → Bool) → BitVec w)
    (hwf : ∀ i, BitWF n₀ (g i))
    (hval : ∀ f i, (g i).denote f = (val f).getLsbD i.val) :
    EncA n₀ w (Pure.pure (Array.ofFn g)) val := by
  have hst : Stable n₀ val := by
    refine Stable.bv (fun f h ha i hi => ?_)
    rw [← hval f ⟨i, hi⟩, ← hval h ⟨i, hi⟩]
    exact (hwf ⟨i, hi⟩).denote_congr ha
  refine ⟨fun s bits s' hrun => ?_, hst, Enc.pure ?_ ?_⟩
  · rw [run_pure] at hrun; cases hrun; simp
  · intro b hb
    obtain ⟨i, hi⟩ := (Array.mem_ofFn ..).mp hb
    exact hi ▸ hwf i
  · intro f
    apply Array.ext
    · simp [bitsOf]
    · intro i h₁ h₂
      simp only [den_bits, Array.size_map, Array.size_ofFn] at h₁
      simp only [den_bits, Array.getElem_map, Array.getElem_ofFn, bitsOf]
      exact hval f ⟨i, h₁⟩

/-- A purely functional continuation `do let x ← ea; pure (k x)` whose
effect on denotations is the function `φ` — the shape of `not`, `slice`,
`zext` and `sext`. -/
theorem EncA.bindPure {n₀ w w' : Nat} {ea : M (Array Bit)} {va : (Var → Bool) → BitVec w}
    (h : EncA n₀ w ea va) (k : Array Bit → Array Bit) (φ : Array Bool → Array Bool)
    (val : BitVec w → BitVec w')
    (hsize : ∀ x : Array Bit, x.size = w → (k x).size = w')
    (hwf : ∀ (n : Nat) (x : Array Bit), (∀ b ∈ x, BitWF n b) → ∀ b ∈ k x, BitWF n b)
    (hφ : ∀ (f : Var → Bool) (x : Array Bit), (k x).map (·.denote f) = φ (x.map (·.denote f)))
    (hval : ∀ v : BitVec w, φ (bitsOf v) = bitsOf (val v)) :
    EncA n₀ w' (do let x ← ea; Pure.pure (k x)) (fun f => val (va f)) := by
  obtain ⟨hsz, hstv, henc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro s bits s' hrun
    rw [run_bind] at hrun
    revert hrun
    cases hr : M.run ea s with
    | mk r s₁ =>
      cases r with
      | error e => intro hh; simp at hh
      | ok x =>
        intro hh
        simp only [run_pure] at hh
        cases hh
        exact hsize x (hsz s x _ hr)
  · exact fun f g ha => congrArg val (hstv f g ha)
  · refine Enc.congr (α := Array Bit) (β := Array Bool) (val := fun f => φ (bitsOf (va f)))
      (fun f => hval (va f)) ?_
    refine Enc.bind (α := Array Bit) (α' := Array Bit) (valA := fun f => bitsOf (va f))
      (valB := fun xv _ => φ xv) hstv.bits henc ?_
    intro x n hn hwx
    exact Enc.pure (hwf n x hwx) (fun f => hφ f x)

theorem buildM_size {g : Nat → M Bit} : ∀ (k : Nat) (s : St) (bits : Array Bit) (s' : St),
    M.run (buildM g k) s = (.ok bits, s') → bits.size = k
  | 0, s, bits, s', hrun => by rw [buildM, run_pure] at hrun; cases hrun; simp
  | k + 1, s, bits, s', hrun => by
    rw [buildM, run_bind] at hrun
    revert hrun
    cases hr : M.run (buildM g k) s with
    | mk r s₁ =>
      cases r with
      | error e => intro hh; simp at hh
      | ok a =>
        simp only []
        rw [run_bind]
        cases hr2 : M.run (g k) s₁ with
        | mk r2 s₂ =>
          cases r2 with
          | error e => intro hh; simp at hh
          | ok b =>
            simp only [run_pure]
            intro hh
            cases hh
            simp [buildM_size k s a s₁ hr]

theorem Stable.bop {n₀ n : Nat} {x y : Bit} {bop : (Var → Bool) → Bool → Bool → Bool}
    (hn : n₀ ≤ n) (hb : ∀ a b : Bool, Stable n₀ (fun f => bop f a b))
    (hx : BitWF n x) (hy : BitWF n y) :
    Stable n (fun f => bop f (x.denote f) (y.denote f)) := by
  intro f g ha
  show bop f (Bit.denote f x) (Bit.denote f y) = bop g (Bit.denote g x) (Bit.denote g y)
  rw [hx.denote_congr ha, hy.denote_congr ha]
  exact hb _ _ f g (ha.antitone hn)

theorem getElem_bang_map (a : Array Bit) (f : Var → Bool) (i : Nat) (h : i < a.size) :
    (a.map (·.denote f))[i]! = (a[i]!).denote f := by
  rw [getElem_bang _ i (by simpa using h), getElem_bang a i h, Array.getElem_map]

theorem bitsOf_getElem_bang {w : Nat} (v : BitVec w) (i : Nat) (h : i < w) :
    (bitsOf v)[i]! = v.getLsbD i := by
  rw [getElem_bang _ i (by simpa using h), bitsOf_getElem]

/-- The elementwise binary shape: blast both operands, then one gate per bit
position. Covers `and`, `or`, `xor` and `mux`. -/
theorem EncA_binop {n₀ w : Nat} {ea eb : M (Array Bit)} {va vb val : (Var → Bool) → BitVec w}
    {op : Bit → Bit → M Bit} {bop : (Var → Bool) → Bool → Bool → Bool}
    (hop : ∀ (n : Nat) (x y : Bit), n₀ ≤ n → BitWF n x → BitWF n y →
        Enc n (op x y) (fun f => bop f (x.denote f) (y.denote f)))
    (hbst : ∀ a b : Bool, Stable n₀ (fun f => bop f a b))
    (ha : EncA n₀ w ea va) (hb : EncA n₀ w eb vb)
    (hval : ∀ (f : Var → Bool) (i : Nat), i < w →
        (val f).getLsbD i = bop f ((va f).getLsbD i) ((vb f).getLsbD i)) :
    EncA n₀ w (do let x ← ea; let y ← eb; buildM (fun i => op x[i]! y[i]!) x.size) val := by
  obtain ⟨hsza, hsta, henca⟩ := ha
  obtain ⟨hszb, hstb, hencb⟩ := hb
  have hstval : Stable n₀ val := by
    refine Stable.bv (fun f g hag i hi => ?_)
    rw [hval f i hi, hval g i hi, hsta f g hag, hstb f g hag]
    exact hbst _ _ f g hag
  refine ⟨?_, hstval, ?_⟩
  · -- width
    intro s bits s' hrun
    rw [run_bind] at hrun
    revert hrun
    cases hr : M.run ea s with
    | mk r s₁ =>
      cases r with
      | error e => intro hh; simp at hh
      | ok x =>
        simp only []
        rw [run_bind]
        cases hr2 : M.run eb s₁ with
        | mk r2 s₂ =>
          cases r2 with
          | error e => intro hh; simp at hh
          | ok y =>
            intro hh
            rw [← hsza s x s₁ hr]
            exact buildM_size _ _ _ _ hh
  · refine Enc.congr (α := Array Bit) (β := Array Bool)
      (val := fun f => Array.ofFn (n := w) fun i : Fin w =>
        bop f ((bitsOf (va f))[i.val]!) ((vb f).getLsbD i.val)) (fun f => ?_) ?_
    · apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_ofFn] at h₁
        rw [Array.getElem_ofFn, bitsOf_getElem, hval f i h₁,
          bitsOf_getElem_bang (va f) i h₁]
    refine Enc.bind' (α := Array Bit) (α' := Array Bit) (P := fun x => x.size = w)
      (valA := fun f => bitsOf (va f))
      (valB := fun xv f => Array.ofFn (n := w) fun i : Fin w =>
        bop f (xv[i.val]!) ((vb f).getLsbD i.val))
      hsta.bits hsza henca ?_
    intro x n hn hwx hxw
    refine Enc.congr (α := Array Bit) (β := Array Bool)
      (val := fun f => Array.ofFn (n := w) fun i : Fin w =>
        bop f ((x[i.val]!).denote f) ((bitsOf (vb f))[i.val]!)) (fun f => ?_) ?_
    · show (Array.ofFn (n := w) fun i : Fin w =>
              bop f ((x[i.val]!).denote f) ((bitsOf (vb f))[i.val]!))
          = Array.ofFn (n := w) fun i : Fin w =>
              bop f ((x.map (·.denote f))[i.val]!) ((vb f).getLsbD i.val)
      apply Array.ext
      · simp
      · intro i h₁ h₂
        simp only [Array.size_ofFn] at h₁
        rw [Array.getElem_ofFn, Array.getElem_ofFn, getElem_bang_map x f i (by omega),
          bitsOf_getElem_bang (vb f) i h₁]
    refine Enc.bind' (α := Array Bit) (α' := Array Bit) (P := fun y => y.size = w)
      (valA := fun f => bitsOf (vb f))
      (valB := fun yv f => Array.ofFn (n := w) fun i : Fin w =>
        bop f ((x[i.val]!).denote f) (yv[i.val]!))
      (Stable.mono hn hstb.bits) hszb (Enc.mono hn hencb) ?_
    · intro y n' hn' hwy hyw
      have hxb : ∀ i, i < w → BitWF n' (x[i]!) := fun i hi => by
        rw [getElem_bang x i (by omega)]
        exact BitWF.mono hn' (hwx _ (Array.getElem_mem (by omega)))
      have hyb : ∀ i, i < w → BitWF n' (y[i]!) := fun i hi => by
        rw [getElem_bang y i (by omega)]
        exact hwy _ (Array.getElem_mem (by omega))
      refine Enc.congr (α := Array Bit) (β := Array Bool)
        (val := fun f => Array.ofFn (n := x.size) fun i : Fin x.size =>
          bop f ((x[i.val]!).denote f) ((y[i.val]!).denote f)) (fun f => ?_) ?_
      · show (Array.ofFn (n := x.size) fun i : Fin x.size =>
              bop f ((x[i.val]!).denote f) ((y[i.val]!).denote f))
            = Array.ofFn (n := w) fun i : Fin w =>
                bop f ((x[i.val]!).denote f) ((y.map (·.denote f))[i.val]!)
        apply Array.ext
        · simp [hxw]
        · intro i h₁ h₂
          simp only [Array.size_ofFn, hxw] at h₁
          rw [Array.getElem_ofFn, Array.getElem_ofFn, getElem_bang_map y f i (by omega)]
      · refine Enc_buildM (n₀ := n')
          (val := fun i f => bop f ((x[i]!).denote f) ((y[i]!).denote f)) x.size
          (fun i hi => hop n' (x[i]!) (y[i]!) (Nat.le_trans hn hn')
            (hxb i (by omega)) (hyb i (by omega)))
          (fun i hi => Stable.bop (Nat.le_trans hn hn') hbst
            (hxb i (by omega)) (hyb i (by omega)))

end Loom.Netlist
