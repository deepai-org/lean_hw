-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.KeyInjective
import Loom.Release.ToProgramLemmas

/-!
# The flatten-soundness invariant, semantic half: `flatten` MATCHES

The keystone for retiring the last two sorries of `toProgram_denotes`: the
name `flatten` returns structurally matches the source expression against
the final indexed wire rope, per the release matcher
(`Symbolic.indexedExprMatches`).

The structural half (`FlattenWF.flatten_spec`) already delivers consistency
(`FlattenSt.WF`), persistence (`FlattenSt.Extends`), and operand
resolvability. What remains semantic is the CSE table: on a hit, the name
handed back was allocated by an *earlier* emission site, and the matcher
only accepts it if that site stored the *same structural node*. That is
exactly key injectivity (`KeyInjective.keyOf_injective`) under the
identifier discipline, threaded through a dedicated side invariant
(`FlattenSt.KeyWF`): every CSE entry remembers a wire whose recorded `Rhs`
renders to the entry's key and obeys the token discipline.

Two decidable disciplines close the remaining matcher guards:
`exprMatchOkB` (the matcher's width arithmetic — `zext` non-narrowing,
`sext` strictly widening) and `moduleNamesOkB` (declared register and
memory names are identifier tokens, D14).
-/

namespace Loom.Release.SSA

open Loom.Hw Loom.Emit.MicroVerilog

/-! ## Width discipline: the shapes the matcher accepts -/

/-- The width arithmetic `Symbolic.indexedExprMatches` insists on beyond
well-typedness: `zext` must not narrow (`w ≤ w'`) and `sext` must strictly
widen (`w < w'`); everything else is pure recursion. -/
def exprMatchOkB : {w : Nat} → Emit.MicroVerilog.Expr w → Bool
  | _, .lit _ => true
  | _, .reg _ _ => true
  | _, .memRead _ _ addr => exprMatchOkB addr
  | _, .and a b | _, .or a b | _, .xor a b | _, .add a b | _, .sub a b
  | _, .shl a b | _, .shr a b | _, .eq a b | _, .ult a b | _, .slt a b =>
      exprMatchOkB a && exprMatchOkB b
  | _, .not a => exprMatchOkB a
  | _, .mux c t f => exprMatchOkB c && exprMatchOkB t && exprMatchOkB f
  | _, @Emit.MicroVerilog.Expr.slice _ a _ _ => exprMatchOkB a
  | w', @Emit.MicroVerilog.Expr.zext w a _ =>
      decide (w ≤ w') && exprMatchOkB a
  | w', @Emit.MicroVerilog.Expr.sext w a _ =>
      decide (w < w') && exprMatchOkB a

/-- Width discipline for every expression the printer traversal flattens:
all register nexts, all port faces, all output values. -/
def moduleMatchOkB (m : Module) : Bool :=
  m.regs.all (fun r => exprMatchOkB r.next) &&
    m.mems.all (fun mm => mm.wrPorts.all fun p =>
      exprMatchOkB p.en && exprMatchOkB p.addr && exprMatchOkB p.data) &&
    m.outs.all (fun o => exprMatchOkB o.val)

/-! ## Name discipline (D14) -/

/-- Declared register and memory names are identifier tokens. With
`ExprEmitOk` in force every `.reg` leaf resolves in `m.regs` and every
`.memRead` name in `m.mems`, so this check covers every non-wire operand
string `flatten` ever emits. -/
def moduleNamesOkB (m : Module) : Bool :=
  m.regs.all (fun r => identTokenB r.name) &&
    m.mems.all (fun mm => identTokenB mm.name)

/-! ## The key-coherence side invariant -/

/-- Semantic coherence of the CSE table: every entry remembers an emitted
wire whose recorded structural `Rhs` renders to the entry's key and obeys
the operand-token discipline. Together with `keyOf_injective` this turns a
CSE hit into structural equality of the stored and re-emitted nodes. -/
structure FlattenSt.KeyWF (st : FlattenSt) : Prop where
  cseKey : ∀ (w : Nat) (key name : String), st.cse[(w, key)]? = some name →
    ∃ (m : Nat) (wire : Wire), name = Symbolic.wireName m ∧
      st.wires[m]? = some wire ∧ wire.width = w ∧
      keyOf wire.rhs = key ∧ rhsTokensOk wire.rhs = true

/-- The empty state is key-coherent. -/
theorem FlattenSt.KeyWF.empty : FlattenSt.KeyWF {} where
  cseKey := by intro w key name found; simp at found

/-! ## `freshWire` bricks -/

/-- `freshWire` only appends. -/
theorem freshWire_extends (w : Nat) (key : String) (rhs : Rhs)
    (st : FlattenSt) : st.Extends ((freshWire w key rhs).run st).2 := by
  rw [freshWire_run]
  cases hit : st.cse[(w, key)]? with
  | some name => exact .rfl st
  | none => exact ⟨Nat.le_succ _, fun i wire found => push_persist i wire found⟩

/-- A canonical wire name resolves as a wire reference. -/
theorem operandRef_wireName (m : Nat) :
    operandRef (Symbolic.wireName m) = .wire m := by
  simp [operandRef, wireNumber?_wireName]

/-- **The CSE-hit lemma.** Run at a key rendered from a token-disciplined
`rhs`, `freshWire` hands back the canonical name of a wire — freshly pushed
or CSE-recalled — that stores *exactly* `rhs` at width `w`, and key
coherence is preserved. On a hit this is `keyOf_injective`; on a miss it is
the pushed wire itself. -/
theorem freshWire_matches {regs : List RegDef} {mems : List MemDef}
    (w : Nat) (rhs : Rhs) (st : FlattenSt)
    (wf : st.WF regs mems) (kwf : st.KeyWF)
    (htok : rhsTokensOk rhs = true) :
    (((freshWire w (keyOf rhs) rhs).run st).2).KeyWF ∧
    ∃ (m : Nat) (wire : Wire),
      ((freshWire w (keyOf rhs) rhs).run st).1 = Symbolic.wireName m ∧
      (((freshWire w (keyOf rhs) rhs).run st).2).wires[m]? = some wire ∧
      wire.width = w ∧ wire.rhs = rhs := by
  rw [freshWire_run]
  cases hit : st.cse[(w, keyOf rhs)]? with
  | some name =>
      obtain ⟨m, wire, hname, hfound, hwidth, hkey, htok'⟩ :=
        kwf.cseKey w (keyOf rhs) name hit
      exact ⟨kwf, m, wire, hname, hfound, hwidth,
        keyOf_injective htok' htok hkey⟩
  | none =>
      have newFound :
          (st.wires.push ⟨w, "n" ++ toString st.next, rhs⟩)[st.next]? =
            some ⟨w, "n" ++ toString st.next, rhs⟩ := by
        rw [wf.sizeEq]
        exact Array.getElem?_push_size
      refine ⟨⟨?_⟩, st.next, ⟨w, "n" ++ toString st.next, rhs⟩,
        (wireName_eq_append st.next).symm, newFound, rfl, rfl⟩
      intro wq keyq nameq foundq
      rw [Std.HashMap.getElem?_insert] at foundq
      split at foundq
      · rename_i keysEq
        cases foundq
        have pairEq : (w, keyOf rhs) = (wq, keyq) := beq_iff_eq.mp keysEq
        exact ⟨st.next, ⟨w, "n" ++ toString st.next, rhs⟩,
          (wireName_eq_append st.next).symm, newFound,
          congrArg Prod.fst pairEq, congrArg Prod.snd pairEq, htok⟩
      · obtain ⟨m, wire, hname, hfound, hwidth, hkey, htok'⟩ :=
          kwf.cseKey wq keyq nameq foundq
        exact ⟨m, wire, hname, push_persist m wire hfound, hwidth, hkey,
          htok'⟩

/-- Per-node finisher for the main induction: at a call site whose key
renders its token-disciplined `rhs`, the returned name is an identifier
token and — through `hsub` (this run's wires persist into `final`) and
`faithful` (the final flat array agrees with the indexed rope) — the
matcher's lookup exposes `indexedRhsOf rhs`, so any per-constructor matcher
argument `hmat` closes the structural match. -/
private theorem freshWire_finish
    {regs : List RegDef} {mems : List MemDef}
    {allWires : Rope (List Symbolic.IndexedWire)} {table : Symbolic.WireTable}
    {final : Array Wire}
    (faithful : ∀ (m : Nat) (wire : Wire), final[m]? = some wire →
      Symbolic.lookupIndexed? allWires table m =
        some ⟨m, wire.width, indexedRhsOf wire.rhs⟩)
    {w : Nat} (e : Emit.MicroVerilog.Expr w) (key : String) (rhs : Rhs)
    (st : FlattenSt) (wf : st.WF regs mems) (kwf : st.KeyWF)
    (hkey : key = keyOf rhs) (htok : rhsTokensOk rhs = true)
    (hsub : ∀ (i : Nat) (wire : Wire),
      (((freshWire w key rhs).run st).2).wires[i]? = some wire →
        final[i]? = some wire)
    (hmat : ∀ m : Nat,
      Symbolic.lookupIndexed? allWires table m =
        some ⟨m, w, indexedRhsOf rhs⟩ →
      Symbolic.indexedExprMatches allWires table e (.wire m) = true) :
    (((freshWire w key rhs).run st).2).KeyWF ∧
    identTokenB ((freshWire w key rhs).run st).1 = true ∧
    Symbolic.indexedExprMatches allWires table e
      (operandRef ((freshWire w key rhs).run st).1) = true := by
  subst hkey
  obtain ⟨kwf', m, wire, hname, hfound, hwidth, hrhs⟩ :=
    freshWire_matches w rhs st wf kwf htok
  refine ⟨kwf', ?_, ?_⟩
  · rw [hname]; exact identTokenB_wireName m
  · have hlook := faithful m wire (hsub m wire hfound)
    rw [hwidth, hrhs] at hlook
    rw [hname, operandRef_wireName]
    exact hmat m hlook

/-! ## The main theorem -/

/-- **The semantic flatten spec.** The name `flatten` returns structurally
matches the source expression against the final indexed wire rope, per the
release matcher. `hsub` says this run's output wires persist into the final
flat array (flattening only appends); `faithful` connects that array to the
indexed rope the matcher navigates. The matcher conclusion mentions only
`allWires`/`table`, so it survives all later appends for free. -/
theorem flatten_matches
    (regs : List RegDef) (mems : List MemDef)
    (allWires : Rope (List Symbolic.IndexedWire)) (table : Symbolic.WireTable)
    (final : Array Wire)
    (faithful : ∀ (m : Nat) (wire : Wire), final[m]? = some wire →
      Symbolic.lookupIndexed? allWires table m =
        some ⟨m, wire.width, indexedRhsOf wire.rhs⟩)
    {w : Nat} (e : Emit.MicroVerilog.Expr w) (st : FlattenSt)
    (wf : st.WF regs mems) (kwf : st.KeyWF)
    (hemit : ExprEmitOk regs mems e) (hmatch : exprMatchOkB e = true)
    (hnamesR : regs.all (fun r => identTokenB r.name) = true)
    (hnamesM : mems.all (fun mm => identTokenB mm.name) = true)
    (hsub : ∀ (i : Nat) (wire : Wire),
      (((flatten e).run st).2).wires[i]? = some wire → final[i]? = some wire) :
    (((flatten e).run st).2).KeyWF ∧
    identTokenB ((flatten e).run st).1 = true ∧
    Symbolic.indexedExprMatches allWires table e
      (operandRef ((flatten e).run st).1) = true := by
  induction e generalizing st with
  | @lit w v =>
      exact freshWire_finish faithful (.lit v) s!"{w}'d{v.toNat}"
        (.lit w v.toNat) st wf kwf (flatten_key_lit w v.toNat) rfl hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook])
  | reg wr name =>
      obtain ⟨hnum, r, hfind, -⟩ := hemit
      have htokName : identTokenB name = true := by
        have hname : r.name = name := by
          have := List.find?_some hfind
          simpa using this
        have hall := List.all_eq_true.mp hnamesR r
          (List.mem_of_find?_eq_some hfind)
        rwa [hname] at hall
      refine ⟨kwf, htokName, ?_⟩
      show Symbolic.indexedExprMatches allWires table (.reg wr name)
        (operandRef name) = true
      have hop : operandRef name = .reg name := by simp [operandRef, hnum]
      rw [hop]
      simp [Symbolic.indexedExprMatches]
  | memRead dw mem addr ih =>
      obtain ⟨⟨header, hfind, -, -⟩, okAddr⟩ := hemit
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems addr st wf okAddr
      have extF := freshWire_extends dw
        s!"{mem}[{((flatten addr).run st).1}]"
        (.memRead mem ((flatten addr).run st).1) ((flatten addr).run st).2
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten addr).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := ih st wf kwf okAddr hmatch hsub1
      have hmemTok : identTokenB mem = true := by
        have hname : header.name = mem := by
          have := List.find?_some hfind
          simpa using this
        have hall := List.all_eq_true.mp hnamesM header
          (List.mem_of_find?_eq_some hfind)
        rwa [hname] at hall
      exact freshWire_finish faithful (.memRead dw mem addr)
        s!"{mem}[{((flatten addr).run st).1}]"
        (.memRead mem ((flatten addr).run st).1) ((flatten addr).run st).2
        wf1 kwf1 (flatten_key_memRead _ _)
        (by simp [rhsTokensOk, hmemTok, tok1]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1])
  | @and w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends w
        s!"{((flatten a).run st).1} & {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .and ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.and a b)
        s!"{((flatten a).run st).1} & {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .and ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_and _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @or w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends w
        s!"{((flatten a).run st).1} | {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .or ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.or a b)
        s!"{((flatten a).run st).1} | {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .or ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_or _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @xor w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends w
        s!"{((flatten a).run st).1} ^ {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .xor ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.xor a b)
        s!"{((flatten a).run st).1} ^ {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .xor ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_xor _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @not w a ih =>
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf hemit
      have extF := freshWire_extends w s!"~{((flatten a).run st).1}"
        (.not ((flatten a).run st).1) ((flatten a).run st).2
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := ih st wf kwf hemit hmatch hsub1
      exact freshWire_finish faithful (.not a) s!"~{((flatten a).run st).1}"
        (.not ((flatten a).run st).1) ((flatten a).run st).2 wf1 kwf1
        (flatten_key_not _) tok1 hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1])
  | @add w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends w
        s!"{((flatten a).run st).1} + {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .add ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.add a b)
        s!"{((flatten a).run st).1} + {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .add ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_add _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @sub w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends w
        s!"{((flatten a).run st).1} - {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .sub ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.sub a b)
        s!"{((flatten a).run st).1} - {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .sub ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_sub _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @shl w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends w
        s!"{((flatten a).run st).1} << {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .shl ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.shl a b)
        s!"{((flatten a).run st).1} << {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .shl ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_shl _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @shr w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends w
        s!"{((flatten a).run st).1} >> {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .shr ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.shr a b)
        s!"{((flatten a).run st).1} >> {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .shr ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_shr _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @eq w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends 1
        s!"{((flatten a).run st).1} == {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .eq ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.eq a b)
        s!"{((flatten a).run st).1} == {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .eq ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_eq _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @ult w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends 1
        s!"{((flatten a).run st).1} < {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .ult ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.ult a b)
        s!"{((flatten a).run st).1} < {((flatten b).run ((flatten a).run st).2).1}"
        (.bin .ult ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_ult _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @slt w a b iha ihb =>
      obtain ⟨oka, okb⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems b
        ((flatten a).run st).2 wf1 okb
      have extF := freshWire_extends 1
        s!"$signed({((flatten a).run st).1}) < $signed({((flatten b).run ((flatten a).run st).2).1})"
        (.slt ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten b).run ((flatten a).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := iha st wf kwf oka hmatch.1 hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := ihb ((flatten a).run st).2 wf1 kwf1 okb
        hmatch.2 hsub2
      exact freshWire_finish faithful (.slt a b)
        s!"$signed({((flatten a).run st).1}) < $signed({((flatten b).run ((flatten a).run st).2).1})"
        (.slt ((flatten a).run st).1
          ((flatten b).run ((flatten a).run st).2).1)
        ((flatten b).run ((flatten a).run st).2).2 wf2 kwf2
        (flatten_key_slt _ _) (by simp [rhsTokensOk, tok1, tok2]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2])
  | @mux w c t f ihc iht ihf =>
      obtain ⟨okc, okt, okf⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true] at hmatch
      obtain ⟨⟨hmc, hmt⟩, hmf⟩ := hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems c st wf okc
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems t
        ((flatten c).run st).2 wf1 okt
      obtain ⟨wf3, ext3, -⟩ := flatten_spec regs mems f
        ((flatten t).run ((flatten c).run st).2).2 wf2 okf
      have extF := freshWire_extends w
        s!"{((flatten c).run st).1} ? {((flatten t).run ((flatten c).run st).2).1} : {((flatten f).run ((flatten t).run ((flatten c).run st).2).2).1}"
        (.mux ((flatten c).run st).1
          ((flatten t).run ((flatten c).run st).2).1
          ((flatten f).run ((flatten t).run ((flatten c).run st).2).2).1)
        ((flatten f).run ((flatten t).run ((flatten c).run st).2).2).2
      have hsub3 : ∀ (i : Nat) (wire : Wire),
          (((flatten f).run
            ((flatten t).run ((flatten c).run st).2).2).2).wires[i]? =
              some wire → final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten t).run ((flatten c).run st).2).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub3 i wire (ext3.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten c).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := ihc st wf kwf okc hmc hsub1
      obtain ⟨kwf2, tok2, mat2⟩ := iht ((flatten c).run st).2 wf1 kwf1 okt
        hmt hsub2
      obtain ⟨kwf3, tok3, mat3⟩ := ihf
        ((flatten t).run ((flatten c).run st).2).2 wf2 kwf2 okf hmf hsub3
      exact freshWire_finish faithful (.mux c t f)
        s!"{((flatten c).run st).1} ? {((flatten t).run ((flatten c).run st).2).1} : {((flatten f).run ((flatten t).run ((flatten c).run st).2).2).1}"
        (.mux ((flatten c).run st).1
          ((flatten t).run ((flatten c).run st).2).1
          ((flatten f).run ((flatten t).run ((flatten c).run st).2).2).1)
        ((flatten f).run ((flatten t).run ((flatten c).run st).2).2).2
        wf3 kwf3 (flatten_key_mux _ _ _)
        (by simp [rhsTokensOk, tok1, tok2, tok3]) hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, mat2,
            mat3])
  | slice a lo w' ih =>
      obtain ⟨-, oka⟩ := hemit
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      have extF := freshWire_extends w'
        s!"{((flatten a).run st).1}[{lo + w' - 1}:{lo}]"
        (.slice ((flatten a).run st).1 (lo + w' - 1) lo)
        ((flatten a).run st).2
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := ih st wf kwf oka hmatch hsub1
      exact freshWire_finish faithful (.slice a lo w')
        s!"{((flatten a).run st).1}[{lo + w' - 1}:{lo}]"
        (.slice ((flatten a).run st).1 (lo + w' - 1) lo)
        ((flatten a).run st).2 wf1 kwf1 (flatten_key_slice _ _ _) tok1 hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1])
  | @zext wa a w' ih =>
      simp only [exprMatchOkB, Bool.and_eq_true, decide_eq_true_eq] at hmatch
      obtain ⟨hle, hma⟩ := hmatch
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf hemit
      have extF := freshWire_extends w' s!"{((flatten a).run st).1}"
        (.ident ((flatten a).run st).1) ((flatten a).run st).2
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := ih st wf kwf hemit hma hsub1
      exact freshWire_finish faithful (.zext a w')
        s!"{((flatten a).run st).1}" (.ident ((flatten a).run st).1)
        ((flatten a).run st).2 wf1 kwf1 (flatten_key_ident _) tok1 hsub
        (fun m hlook => by
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, hle])
  | @sext wa a w' ih =>
      obtain ⟨posW, -, oka⟩ := hemit
      simp only [exprMatchOkB, Bool.and_eq_true, decide_eq_true_eq] at hmatch
      obtain ⟨hlt, hma⟩ := hmatch
      rw [flatten_sext_run, if_pos hlt] at hsub ⊢
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems a st wf oka
      have extF := freshWire_extends w'
        ("{" ++ ("{" ++ toString (w' - wa) ++ "{" ++ ((flatten a).run st).1 ++
          "[" ++ toString (wa - 1) ++ "]}}") ++ ", " ++
          ((flatten a).run st).1 ++ "}")
        (.sext (w' - wa) ((flatten a).run st).1 (wa - 1))
        ((flatten a).run st).2
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten a).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub i wire (extF.2 i wire h)
      obtain ⟨kwf1, tok1, mat1⟩ := ih st wf kwf oka hma hsub1
      exact freshWire_finish faithful (.sext a w')
        ("{" ++ ("{" ++ toString (w' - wa) ++ "{" ++ ((flatten a).run st).1 ++
          "[" ++ toString (wa - 1) ++ "]}}") ++ ", " ++
          ((flatten a).run st).1 ++ "}")
        (.sext (w' - wa) ((flatten a).run st).1 (wa - 1))
        ((flatten a).run st).2 wf1 kwf1 (flatten_key_sext_wide _ _ _) tok1
        hsub
        (fun m hlook => by
          have h1 : wa - 1 + 1 = wa := by have := posW hlt; omega
          simp [Symbolic.indexedExprMatches, indexedRhsOf, hlook, mat1, hlt,
            h1])

/-! ## Traversal corollaries -/

/-- Every register produced by `flattenRegs` carries a next-value name that
matches its declaration's next expression. -/
theorem flattenRegs_matches
    (regs : List RegDef) (mems : List MemDef)
    (allWires : Rope (List Symbolic.IndexedWire)) (table : Symbolic.WireTable)
    (final : Array Wire)
    (faithful : ∀ (m : Nat) (wire : Wire), final[m]? = some wire →
      Symbolic.lookupIndexed? allWires table m =
        some ⟨m, wire.width, indexedRhsOf wire.rhs⟩)
    (hnamesR : regs.all (fun r => identTokenB r.name) = true)
    (hnamesM : mems.all (fun mm => identTokenB mm.name) = true)
    (rs : List RegDef) (st : FlattenSt)
    (wf : st.WF regs mems) (kwf : st.KeyWF)
    (hok : ∀ r ∈ rs, ExprEmitOk regs mems r.next)
    (hmat : ∀ r ∈ rs, exprMatchOkB r.next = true)
    (hsub : ∀ (i : Nat) (wire : Wire),
      (((flattenRegs rs).run st).2).wires[i]? = some wire →
        final[i]? = some wire) :
    (((flattenRegs rs).run st).2).KeyWF ∧
    ∀ (i : Nat) (out : Reg) (src : RegDef),
      ((flattenRegs rs).run st).1[i]? = some out → rs[i]? = some src →
      Symbolic.indexedExprMatches allWires table src.next
        (operandRef out.next) = true := by
  induction rs generalizing st with
  | nil =>
      refine ⟨kwf, ?_⟩
      intro i out src hout hsrc
      exact absurd hsrc (by simp)
  | cons r rest ih =>
      obtain ⟨wfR, extR, -⟩ := flatten_spec regs mems r.next st wf
        (hok r List.mem_cons_self)
      obtain ⟨wfRest, extRest⟩ := flattenRegs_spec regs mems rest
        ((flatten r.next).run st).2 wfR
        (fun r' hr => hok r' (List.mem_cons_of_mem _ hr))
      have hsubRest : ∀ (i : Nat) (wire : Wire),
          (((flattenRegs rest).run ((flatten r.next).run st).2).2).wires[i]? =
            some wire → final[i]? = some wire :=
        fun i wire h => hsub i wire h
      have hsubHead : ∀ (i : Nat) (wire : Wire),
          (((flatten r.next).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsubRest i wire (extRest.2 i wire h)
      obtain ⟨kwf1, -, matHead⟩ := flatten_matches regs mems allWires table
        final faithful r.next st wf kwf (hok r List.mem_cons_self)
        (hmat r List.mem_cons_self) hnamesR hnamesM hsubHead
      obtain ⟨kwf2, matRest⟩ := ih ((flatten r.next).run st).2 wfR kwf1
        (fun r' hr => hok r' (List.mem_cons_of_mem _ hr))
        (fun r' hr => hmat r' (List.mem_cons_of_mem _ hr)) hsubRest
      refine ⟨kwf2, ?_⟩
      intro i out src hout hsrc
      cases i with
      | zero =>
          rw [flattenRegs_run_cons] at hout
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hout hsrc
          subst hout
          subst hsrc
          exact matHead
      | succ n =>
          rw [flattenRegs_run_cons] at hout
          simp only [List.getElem?_cons_succ] at hout hsrc
          exact matRest n out src hout hsrc

private theorem flattenWrites_run_cons {aw dw : Nat} (p : WritePort aw dw)
    (rest : List (WritePort aw dw)) (s : FlattenSt) :
    (flattenWrites (p :: rest)).run s =
      (({ en := ((flatten p.en).run s).1,
          addr := ((flatten p.addr).run ((flatten p.en).run s).2).1,
          data := ((flatten p.data).run
            ((flatten p.addr).run ((flatten p.en).run s).2).2).1 } : Write) ::
        ((flattenWrites rest).run ((flatten p.data).run
          ((flatten p.addr).run ((flatten p.en).run s).2).2).2).1,
       ((flattenWrites rest).run ((flatten p.data).run
          ((flatten p.addr).run ((flatten p.en).run s).2).2).2).2) := rfl

/-- Every write port produced by `flattenWrites` matches its source port on
all three faces. -/
theorem flattenWrites_matches
    (regs : List RegDef) (mems : List MemDef)
    (allWires : Rope (List Symbolic.IndexedWire)) (table : Symbolic.WireTable)
    (final : Array Wire)
    (faithful : ∀ (m : Nat) (wire : Wire), final[m]? = some wire →
      Symbolic.lookupIndexed? allWires table m =
        some ⟨m, wire.width, indexedRhsOf wire.rhs⟩)
    (hnamesR : regs.all (fun r => identTokenB r.name) = true)
    (hnamesM : mems.all (fun mm => identTokenB mm.name) = true)
    {aw dw : Nat} (ports : List (WritePort aw dw)) (st : FlattenSt)
    (wf : st.WF regs mems) (kwf : st.KeyWF)
    (hok : ∀ p ∈ ports, ExprEmitOk regs mems p.en ∧
      ExprEmitOk regs mems p.addr ∧ ExprEmitOk regs mems p.data)
    (hmat : ∀ p ∈ ports, exprMatchOkB p.en = true ∧
      exprMatchOkB p.addr = true ∧ exprMatchOkB p.data = true)
    (hsub : ∀ (i : Nat) (wire : Wire),
      (((flattenWrites ports).run st).2).wires[i]? = some wire →
        final[i]? = some wire) :
    (((flattenWrites ports).run st).2).KeyWF ∧
    ∀ (i : Nat) (out : Write) (src : WritePort aw dw),
      ((flattenWrites ports).run st).1[i]? = some out →
      ports[i]? = some src →
      Symbolic.indexedExprMatches allWires table src.en
          (operandRef out.en) = true ∧
      Symbolic.indexedExprMatches allWires table src.addr
          (operandRef out.addr) = true ∧
      Symbolic.indexedExprMatches allWires table src.data
          (operandRef out.data) = true := by
  induction ports generalizing st with
  | nil =>
      refine ⟨kwf, ?_⟩
      intro i out src hout hsrc
      exact absurd hsrc (by simp)
  | cons p rest ih =>
      obtain ⟨okEn, okAddr, okData⟩ := hok p List.mem_cons_self
      obtain ⟨hmEn, hmAddr, hmData⟩ := hmat p List.mem_cons_self
      obtain ⟨wf1, ext1, -⟩ := flatten_spec regs mems p.en st wf okEn
      obtain ⟨wf2, ext2, -⟩ := flatten_spec regs mems p.addr
        ((flatten p.en).run st).2 wf1 okAddr
      obtain ⟨wf3, ext3, -⟩ := flatten_spec regs mems p.data
        ((flatten p.addr).run ((flatten p.en).run st).2).2 wf2 okData
      obtain ⟨wfRest, extRest⟩ := flattenWrites_spec regs mems rest
        ((flatten p.data).run
          ((flatten p.addr).run ((flatten p.en).run st).2).2).2 wf3
        (fun p' hp => hok p' (List.mem_cons_of_mem _ hp))
      have hsubRest : ∀ (i : Nat) (wire : Wire),
          (((flattenWrites rest).run ((flatten p.data).run
            ((flatten p.addr).run ((flatten p.en).run st).2).2).2).2).wires[i]? =
              some wire → final[i]? = some wire :=
        fun i wire h => hsub i wire h
      have hsub3 : ∀ (i : Nat) (wire : Wire),
          (((flatten p.data).run
            ((flatten p.addr).run ((flatten p.en).run st).2).2).2).wires[i]? =
              some wire → final[i]? = some wire :=
        fun i wire h => hsubRest i wire (extRest.2 i wire h)
      have hsub2 : ∀ (i : Nat) (wire : Wire),
          (((flatten p.addr).run ((flatten p.en).run st).2).2).wires[i]? =
            some wire → final[i]? = some wire :=
        fun i wire h => hsub3 i wire (ext3.2 i wire h)
      have hsub1 : ∀ (i : Nat) (wire : Wire),
          (((flatten p.en).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsub2 i wire (ext2.2 i wire h)
      obtain ⟨kwf1, -, matEn⟩ := flatten_matches regs mems allWires table
        final faithful p.en st wf kwf okEn hmEn hnamesR hnamesM hsub1
      obtain ⟨kwf2, -, matAddr⟩ := flatten_matches regs mems allWires table
        final faithful p.addr ((flatten p.en).run st).2 wf1 kwf1 okAddr
        hmAddr hnamesR hnamesM hsub2
      obtain ⟨kwf3, -, matData⟩ := flatten_matches regs mems allWires table
        final faithful p.data
        ((flatten p.addr).run ((flatten p.en).run st).2).2 wf2 kwf2 okData
        hmData hnamesR hnamesM hsub3
      obtain ⟨kwf4, matRest⟩ := ih
        ((flatten p.data).run
          ((flatten p.addr).run ((flatten p.en).run st).2).2).2 wf3 kwf3
        (fun p' hp => hok p' (List.mem_cons_of_mem _ hp))
        (fun p' hp => hmat p' (List.mem_cons_of_mem _ hp)) hsubRest
      refine ⟨kwf4, ?_⟩
      intro i out src hout hsrc
      cases i with
      | zero =>
          rw [flattenWrites_run_cons] at hout
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hout hsrc
          subst hout
          subst hsrc
          exact ⟨matEn, matAddr, matData⟩
      | succ n =>
          rw [flattenWrites_run_cons] at hout
          simp only [List.getElem?_cons_succ] at hout hsrc
          exact matRest n out src hout hsrc

/-- Every memory produced by `flattenMems` matches its declaration port by
port, face by face. -/
theorem flattenMems_matches
    (regs : List RegDef) (mems : List MemDef)
    (allWires : Rope (List Symbolic.IndexedWire)) (table : Symbolic.WireTable)
    (final : Array Wire)
    (faithful : ∀ (m : Nat) (wire : Wire), final[m]? = some wire →
      Symbolic.lookupIndexed? allWires table m =
        some ⟨m, wire.width, indexedRhsOf wire.rhs⟩)
    (hnamesR : regs.all (fun r => identTokenB r.name) = true)
    (hnamesM : mems.all (fun mm => identTokenB mm.name) = true)
    (blockSize : Nat) (ms : List MemDef) (st : FlattenSt)
    (wf : st.WF regs mems) (kwf : st.KeyWF)
    (hok : ∀ mm ∈ ms, ∀ p ∈ mm.wrPorts, ExprEmitOk regs mems p.en ∧
      ExprEmitOk regs mems p.addr ∧ ExprEmitOk regs mems p.data)
    (hmat : ∀ mm ∈ ms, ∀ p ∈ mm.wrPorts, exprMatchOkB p.en = true ∧
      exprMatchOkB p.addr = true ∧ exprMatchOkB p.data = true)
    (hsub : ∀ (i : Nat) (wire : Wire),
      (((flattenMems blockSize ms).run st).2).wires[i]? = some wire →
        final[i]? = some wire) :
    (((flattenMems blockSize ms).run st).2).KeyWF ∧
    ∀ (i : Nat) (out : Mem) (src : MemDef),
      ((flattenMems blockSize ms).run st).1[i]? = some out →
      ms[i]? = some src →
      ∀ (j : Nat) (ow : Write) (sp : WritePort src.addrWidth src.dataWidth),
        out.writes[j]? = some ow → src.wrPorts[j]? = some sp →
        Symbolic.indexedExprMatches allWires table sp.en
            (operandRef ow.en) = true ∧
        Symbolic.indexedExprMatches allWires table sp.addr
            (operandRef ow.addr) = true ∧
        Symbolic.indexedExprMatches allWires table sp.data
            (operandRef ow.data) = true := by
  induction ms generalizing st with
  | nil =>
      refine ⟨kwf, ?_⟩
      intro i out src hout hsrc
      exact absurd hsrc (by simp)
  | cons mm rest ih =>
      obtain ⟨wfW, extW⟩ := flattenWrites_spec regs mems mm.wrPorts st wf
        (hok mm List.mem_cons_self)
      obtain ⟨wfRest, extRest⟩ := flattenMems_spec regs mems blockSize rest
        ((flattenWrites mm.wrPorts).run st).2 wfW
        (fun mm' hm => hok mm' (List.mem_cons_of_mem _ hm))
      have hsubRest : ∀ (i : Nat) (wire : Wire),
          (((flattenMems blockSize rest).run
            ((flattenWrites mm.wrPorts).run st).2).2).wires[i]? = some wire →
              final[i]? = some wire :=
        fun i wire h => hsub i wire h
      have hsubW : ∀ (i : Nat) (wire : Wire),
          (((flattenWrites mm.wrPorts).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsubRest i wire (extRest.2 i wire h)
      obtain ⟨kwfW, matPorts⟩ := flattenWrites_matches regs mems allWires
        table final faithful hnamesR hnamesM mm.wrPorts st wf kwf
        (hok mm List.mem_cons_self) (hmat mm List.mem_cons_self) hsubW
      obtain ⟨kwfRest, matRest⟩ := ih ((flattenWrites mm.wrPorts).run st).2
        wfW kwfW (fun mm' hm => hok mm' (List.mem_cons_of_mem _ hm))
        (fun mm' hm => hmat mm' (List.mem_cons_of_mem _ hm)) hsubRest
      refine ⟨kwfRest, ?_⟩
      intro i out src hout hsrc
      cases i with
      | zero =>
          rw [flattenMems_run_cons] at hout
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hout hsrc
          subst hout
          subst hsrc
          intro j ow sp how hsp
          exact matPorts j ow sp how hsp
      | succ n =>
          rw [flattenMems_run_cons] at hout
          simp only [List.getElem?_cons_succ] at hout hsrc
          exact matRest n out src hout hsrc

/-- Every output produced by `flattenOuts` carries a value name matching its
declaration's value expression. -/
theorem flattenOuts_matches
    (regs : List RegDef) (mems : List MemDef)
    (allWires : Rope (List Symbolic.IndexedWire)) (table : Symbolic.WireTable)
    (final : Array Wire)
    (faithful : ∀ (m : Nat) (wire : Wire), final[m]? = some wire →
      Symbolic.lookupIndexed? allWires table m =
        some ⟨m, wire.width, indexedRhsOf wire.rhs⟩)
    (hnamesR : regs.all (fun r => identTokenB r.name) = true)
    (hnamesM : mems.all (fun mm => identTokenB mm.name) = true)
    (os : List OutDef) (st : FlattenSt)
    (wf : st.WF regs mems) (kwf : st.KeyWF)
    (hok : ∀ o ∈ os, ExprEmitOk regs mems o.val)
    (hmat : ∀ o ∈ os, exprMatchOkB o.val = true)
    (hsub : ∀ (i : Nat) (wire : Wire),
      (((flattenOuts os).run st).2).wires[i]? = some wire →
        final[i]? = some wire) :
    (((flattenOuts os).run st).2).KeyWF ∧
    ∀ (i : Nat) (out : Out) (src : OutDef),
      ((flattenOuts os).run st).1[i]? = some out → os[i]? = some src →
      Symbolic.indexedExprMatches allWires table src.val
        (operandRef out.value) = true := by
  induction os generalizing st with
  | nil =>
      refine ⟨kwf, ?_⟩
      intro i out src hout hsrc
      exact absurd hsrc (by simp)
  | cons o rest ih =>
      obtain ⟨wfO, extO, -⟩ := flatten_spec regs mems o.val st wf
        (hok o List.mem_cons_self)
      obtain ⟨wfRest, extRest⟩ := flattenOuts_spec regs mems rest
        ((flatten o.val).run st).2 wfO
        (fun o' ho => hok o' (List.mem_cons_of_mem _ ho))
      have hsubRest : ∀ (i : Nat) (wire : Wire),
          (((flattenOuts rest).run ((flatten o.val).run st).2).2).wires[i]? =
            some wire → final[i]? = some wire :=
        fun i wire h => hsub i wire h
      have hsubHead : ∀ (i : Nat) (wire : Wire),
          (((flatten o.val).run st).2).wires[i]? = some wire →
            final[i]? = some wire :=
        fun i wire h => hsubRest i wire (extRest.2 i wire h)
      obtain ⟨kwf1, -, matHead⟩ := flatten_matches regs mems allWires table
        final faithful o.val st wf kwf (hok o List.mem_cons_self)
        (hmat o List.mem_cons_self) hnamesR hnamesM hsubHead
      obtain ⟨kwf2, matRest⟩ := ih ((flatten o.val).run st).2 wfO kwf1
        (fun o' ho => hok o' (List.mem_cons_of_mem _ ho))
        (fun o' ho => hmat o' (List.mem_cons_of_mem _ ho)) hsubRest
      refine ⟨kwf2, ?_⟩
      intro i out src hout hsrc
      cases i with
      | zero =>
          rw [flattenOuts_run_cons] at hout
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hout hsrc
          subst hout
          subst hsrc
          exact matHead
      | succ n =>
          rw [flattenOuts_run_cons] at hout
          simp only [List.getElem?_cons_succ] at hout hsrc
          exact matRest n out src hout hsrc

/-! ## The whole-module corollary -/

/-- **Module-level MATCHES.** Under the emission obligations, the matcher's
width discipline, and the declared-name token discipline — all decidable —
every register next, every port face, and every output value produced by the
printer-order traversal structurally matches its source expression against
the indexed rope `faithful` describes. Instantiating `allWires :=
d.indexedsOf`, `table := d.tableOf` with `faithful` from
`lookupIndexed?_toIndexedWires` yields the per-root matcher facts
`toProgram_denotes` needs. -/
theorem flattenModule_matches (m : Module) (blockSize : Nat)
    (allWires : Rope (List Symbolic.IndexedWire)) (table : Symbolic.WireTable)
    (faithful : ∀ (i : Nat) (wire : Wire),
      ((((flattenModule m blockSize).run {}).2)).wires[i]? = some wire →
        Symbolic.lookupIndexed? allWires table i =
          some ⟨i, wire.width, indexedRhsOf wire.rhs⟩)
    (hok : ModuleEmitOk m) (hmatch : moduleMatchOkB m = true)
    (hnames : moduleNamesOkB m = true) :
    (∀ (i : Nat) (out : Reg) (src : RegDef),
        ((flattenModule m blockSize).run {}).1.1[i]? = some out →
        m.regs[i]? = some src →
        Symbolic.indexedExprMatches allWires table src.next
          (operandRef out.next) = true) ∧
    (∀ (i : Nat) (out : Mem) (src : MemDef),
        ((flattenModule m blockSize).run {}).1.2.1[i]? = some out →
        m.mems[i]? = some src →
        ∀ (j : Nat) (ow : Write)
          (sp : WritePort src.addrWidth src.dataWidth),
          out.writes[j]? = some ow → src.wrPorts[j]? = some sp →
          Symbolic.indexedExprMatches allWires table sp.en
              (operandRef ow.en) = true ∧
          Symbolic.indexedExprMatches allWires table sp.addr
              (operandRef ow.addr) = true ∧
          Symbolic.indexedExprMatches allWires table sp.data
              (operandRef ow.data) = true) ∧
    (∀ (i : Nat) (out : Out) (src : OutDef),
        ((flattenModule m blockSize).run {}).1.2.2[i]? = some out →
        m.outs[i]? = some src →
        Symbolic.indexedExprMatches allWires table src.val
          (operandRef out.value) = true) := by
  obtain ⟨okR, okP, okO⟩ := hok
  simp only [moduleNamesOkB, Bool.and_eq_true] at hnames
  obtain ⟨hnamesR, hnamesM⟩ := hnames
  simp only [moduleMatchOkB, Bool.and_eq_true, List.all_eq_true] at hmatch
  obtain ⟨⟨hmR, hmM⟩, hmO⟩ := hmatch
  obtain ⟨wfR, -⟩ := flattenRegs_spec m.regs m.mems m.regs {}
    (FlattenSt.WF.empty m.regs m.mems) okR
  obtain ⟨wfM, extM⟩ := flattenMems_spec m.regs m.mems blockSize m.mems
    ((flattenRegs m.regs).run {}).2 wfR okP
  obtain ⟨wfO, extO⟩ := flattenOuts_spec m.regs m.mems m.outs
    ((flattenMems blockSize m.mems).run ((flattenRegs m.regs).run {}).2).2
    wfM okO
  have hsubOuts : ∀ (i : Nat) (wire : Wire),
      (((flattenOuts m.outs).run
        ((flattenMems blockSize m.mems).run
          ((flattenRegs m.regs).run {}).2).2).2).wires[i]? = some wire →
        ((((flattenModule m blockSize).run {}).2)).wires[i]? = some wire :=
    fun i wire h => h
  have hsubMems : ∀ (i : Nat) (wire : Wire),
      (((flattenMems blockSize m.mems).run
        ((flattenRegs m.regs).run {}).2).2).wires[i]? = some wire →
        ((((flattenModule m blockSize).run {}).2)).wires[i]? = some wire :=
    fun i wire h => hsubOuts i wire (extO.2 i wire h)
  have hsubRegs : ∀ (i : Nat) (wire : Wire),
      (((flattenRegs m.regs).run {}).2).wires[i]? = some wire →
        ((((flattenModule m blockSize).run {}).2)).wires[i]? = some wire :=
    fun i wire h => hsubMems i wire (extM.2 i wire h)
  obtain ⟨kwfR, matRegs⟩ := flattenRegs_matches m.regs m.mems allWires table
    (((flattenModule m blockSize).run {}).2).wires faithful hnamesR hnamesM
    m.regs {} (FlattenSt.WF.empty m.regs m.mems) FlattenSt.KeyWF.empty okR
    hmR hsubRegs
  obtain ⟨kwfM, matMems⟩ := flattenMems_matches m.regs m.mems allWires table
    (((flattenModule m blockSize).run {}).2).wires faithful hnamesR hnamesM
    blockSize m.mems ((flattenRegs m.regs).run {}).2 wfR kwfR okP
    (fun mm hm p hp => ⟨(hmM mm hm p hp).1.1, (hmM mm hm p hp).1.2,
      (hmM mm hm p hp).2⟩)
    hsubMems
  obtain ⟨-, matOuts⟩ := flattenOuts_matches m.regs m.mems allWires table
    (((flattenModule m blockSize).run {}).2).wires faithful hnamesR hnamesM
    m.outs
    ((flattenMems blockSize m.mems).run ((flattenRegs m.regs).run {}).2).2
    wfM kwfM okO hmO hsubOuts
  exact ⟨matRegs, matMems, matOuts⟩

/-! ## Axiom audit -/

#print axioms flatten_matches
#print axioms flattenRegs_matches
#print axioms flattenWrites_matches
#print axioms flattenMems_matches
#print axioms flattenOuts_matches
#print axioms flattenModule_matches

end Loom.Release.SSA
