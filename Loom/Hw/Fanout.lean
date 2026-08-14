-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Retime

/-!
# Verified register fan-out duplication

`duplicateFanout` adds a fresh replica of one register, redirects reads in a
selected set of rules to that replica, and mirrors every write to the source
onto both copies.  The transform is cycle preserving from reset: the two
copies start equal, mirrored writes preserve their coherence, and selected
readers therefore see the same value as before.

This is deliberately a register-level primitive.  It gives a placement or
synthesis flow two equivalent drivers for disjoint consumer cones without
claiming that duplication always improves timing.
-/

namespace Loom.Hw

/-- Default generated name for a duplicated register. -/
def fanoutName (source : String) : String := source ++ "__dup"

/-- Redirect register reads of `source` to `replica`. Widths are preserved;
memory names and write targets are not involved. -/
def Expr.redirectRead (source replica : String) : {w : Nat} → Expr w → Expr w
  | _, .lit value => .lit value
  | w, .reg _ name => .reg w (if name = source then replica else name)
  | _, .memRead width name address =>
      .memRead width name (address.redirectRead source replica)
  | _, .and left right => .and (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .or left right => .or (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .xor left right => .xor (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .not value => .not (value.redirectRead source replica)
  | _, .add left right => .add (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .sub left right => .sub (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .mul left right => .mul (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .udiv left right => .udiv (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .urem left right => .urem (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .shl left right => .shl (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .shr left right => .shr (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .eq left right => .eq (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .ult left right => .ult (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .slt left right => .slt (left.redirectRead source replica) (right.redirectRead source replica)
  | _, .mux cond yes no =>
      .mux (cond.redirectRead source replica) (yes.redirectRead source replica)
        (no.redirectRead source replica)
  | _, .slice value lo width => .slice (value.redirectRead source replica) lo width
  | _, .zext value width => .zext (value.redirectRead source replica) width
  | _, .sext value width => .sext (value.redirectRead source replica) width

/-- Transform one action. If `redirect` is true its reads use the replica;
every write to the source is mirrored regardless of which consumer owns it. -/
def Act.duplicateFanoutAct (source replica : String) (redirect : Bool) : Act → Act
  | .skip => .skip
  | .seq first second =>
      .seq (first.duplicateFanoutAct source replica redirect)
        (second.duplicateFanoutAct source replica redirect)
  | .ite cond yes no =>
      let cond' := if redirect then cond.redirectRead source replica else cond
      .ite cond' (yes.duplicateFanoutAct source replica redirect)
        (no.duplicateFanoutAct source replica redirect)
  | .write width target value =>
      let value' := if redirect then value.redirectRead source replica else value
      if target = source then
        .seq (.write width source value') (.write width replica value')
      else
        .write width target value'
  | .writeSlice width target lo fieldWidth inBounds value =>
      let value' := if redirect then value.redirectRead source replica else value
      if target = source then
        .seq
          (.writeSlice width source lo fieldWidth inBounds value')
          (.writeSlice width replica lo fieldWidth inBounds value')
      else
        .writeSlice width target lo fieldWidth inBounds value'
  | .memWrite aw dw memory port address data =>
      let address' := if redirect then address.redirectRead source replica else address
      let data' := if redirect then data.redirectRead source replica else data
      .memWrite aw dw memory port address' data'

/-- Duplicate `source` and move the rules named by `consumers` onto the
replica. Rule order and all source declarations remain unchanged. -/
def duplicateFanout (design : Design) (source : String) (width : Nat)
    (replica : String := fanoutName source) (consumers : List String) : Design :=
  { design with
    regs := design.regs ++ [⟨replica, width, retimeRegInit design source width⟩]
    rules := design.rules.map fun rule =>
      { rule with body := (Act.duplicateFanoutAct source replica
          (consumers.contains rule.name) rule.body) } }

/-- Typed entry point: the source name and width come from one `Reg` handle. -/
def duplicateFanoutReg {width : Nat} (design : Design) (source : Reg width)
    (replica : String := fanoutName source.name) (consumers : List String) : Design :=
  duplicateFanout design source.name width replica consumers

/-- Executable guard for the proved class: source declaration matches and
the replica is absent from every namespace and every original rule body. -/
def duplicateFanoutOkB (design : Design) (source : String) (width : Nat)
    (replica : String := fanoutName source) : Bool :=
  decide (design.regs.map (·.name)).Nodup &&
  (design.regs.any fun rd => rd.name == source && rd.width == width) &&
  (!(design.regs.any fun rd => rd.name == replica)) &&
  (!(design.inputs.any fun input => input.name == replica)) &&
  (!(design.mems.any fun memory => memory.name == replica)) &&
  (!(design.readsReg replica)) &&
  (!(design.writesReg replica)) &&
  (source != replica)

/-- Typed executable guard matching `duplicateFanoutReg`. -/
def duplicateFanoutRegOkB {width : Nat} (design : Design) (source : Reg width)
    (replica : String := fanoutName source.name) : Bool :=
  duplicateFanoutOkB design source.name width replica

/-- The implementation-only replica is erased by the abstraction. -/
def fanoutAbs (replica : String) (state : St) : St :=
  { state with regs := fun name width =>
      if name = replica then 0#width else state.regs name width }

/-- The inductive invariant introduced by duplication. -/
def FanoutCoherent (source replica : String) (state : St) : Prop :=
  ∀ width, state.regs source width = state.regs replica width

/-- Accumulator relation used by the action and rule-fold proofs. -/
structure FanoutRel (source replica : String) (impl spec : St) : Prop where
  regs : ∀ name width, name ≠ replica → impl.regs name width = spec.regs name width
  coherent : FanoutCoherent source replica impl
  spec_replica : ∀ width, spec.regs replica width = 0#width
  mems : impl.mems = spec.mems

/-! ## Expression agreement -/

theorem Expr.eval_fanoutAbs (replica : String) (state : St) :
    ∀ {w : Nat} (expr : Expr w), expr.readsReg replica = false →
      expr.eval (fanoutAbs replica state) = expr.eval state := by
  intro w expr
  induction expr with
  | lit value => intro _; rfl
  | reg width name =>
      intro h
      simp only [Expr.readsReg, beq_eq_false_iff_ne, ne_eq] at h
      change (fanoutAbs replica state).regs name width = state.regs name width
      simp [fanoutAbs, h]
  | memRead width name address ih =>
      intro h
      simp only [Expr.readsReg] at h
      show (fanoutAbs replica state).mems name
          (address.eval (fanoutAbs replica state)).toNat width = _
      rw [ih h]
      rfl
  | and left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | or left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | xor left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | not value ih => intro h; simp only [Expr.readsReg] at h; simp only [Expr.eval, ih h]
  | add left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | sub left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | mul left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | udiv left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | urem left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | shl left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | shr left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | eq left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | ult left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | slt left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihLeft h.1, ihRight h.2]
  | mux cond yes no ihCond ihYes ihNo =>
      intro h
      simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.eval, ihCond h.1.1, ihYes h.1.2, ihNo h.2]
  | slice value lo width ih =>
      intro h; simp only [Expr.readsReg] at h; simp only [Expr.eval, ih h]
  | zext value width ih =>
      intro h; simp only [Expr.readsReg] at h; simp only [Expr.eval, ih h]
  | sext value width ih =>
      intro h; simp only [Expr.readsReg] at h; simp only [Expr.eval, ih h]

/-- Redirected reads evaluate like the source expression whenever the two
register copies are coherent. -/
theorem Expr.eval_redirectRead (source replica : String) (state : St)
    (hne : source ≠ replica) (coherent : FanoutCoherent source replica state) :
    ∀ {w : Nat} (expr : Expr w), expr.readsReg replica = false →
      (expr.redirectRead source replica).eval state =
        expr.eval (fanoutAbs replica state) := by
  intro w expr
  induction expr with
  | lit value => intro _; rfl
  | reg width name =>
      intro h
      simp only [Expr.readsReg, beq_eq_false_iff_ne, ne_eq] at h
      simp only [Expr.redirectRead, Expr.eval]
      by_cases hs : name = source
      · subst hs
        rw [if_pos rfl, ← coherent width]
        simp [fanoutAbs, hne]
      · rw [if_neg hs]
        simp [fanoutAbs, h]
  | memRead width name address ih =>
      intro h
      simp only [Expr.readsReg] at h
      simp only [Expr.redirectRead, Expr.eval]
      rw [ih h]
      rfl
  | and left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | or left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | xor left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | not value ih => intro h; simp only [Expr.readsReg] at h; simp only [Expr.redirectRead, Expr.eval, ih h]
  | add left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | sub left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | mul left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | udiv left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | urem left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | shl left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | shr left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | eq left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | ult left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | slt left right ihLeft ihRight =>
      intro h; simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihLeft h.1, ihRight h.2]
  | mux cond yes no ihCond ihYes ihNo =>
      intro h
      simp only [Expr.readsReg, Bool.or_eq_false_iff] at h
      simp only [Expr.redirectRead, Expr.eval, ihCond h.1.1, ihYes h.1.2, ihNo h.2]
  | slice value lo width ih =>
      intro h; simp only [Expr.readsReg] at h; simp only [Expr.redirectRead, Expr.eval, ih h]
  | zext value width ih =>
      intro h; simp only [Expr.readsReg] at h; simp only [Expr.redirectRead, Expr.eval, ih h]
  | sext value width ih =>
      intro h; simp only [Expr.readsReg] at h; simp only [Expr.redirectRead, Expr.eval, ih h]

/-- Uniform evaluation lemma used by rules whose membership in the selected
consumer set is represented by a boolean. -/
theorem Expr.eval_redirectIf (source replica : String) (state : St)
    (hne : source ≠ replica) (coherent : FanoutCoherent source replica state)
    (redirect : Bool) {w : Nat} (expr : Expr w) (fresh : expr.readsReg replica = false) :
    (if redirect then expr.redirectRead source replica else expr).eval state =
      expr.eval (fanoutAbs replica state) := by
  cases redirect with
  | false =>
      change expr.eval state = expr.eval (fanoutAbs replica state)
      exact (expr.eval_fanoutAbs replica state fresh).symm
  | true =>
      change (expr.redirectRead source replica).eval state =
        expr.eval (fanoutAbs replica state)
      exact expr.eval_redirectRead source replica state hne coherent fresh

/-! ## Action and cycle agreement -/

/-- One transformed action preserves both the source semantics and replica
coherence. The original action must not mention the fresh replica. -/
theorem FanoutRel.run_duplicate (source replica : String) (hne : source ≠ replica)
    (state : St) (stateCoherent : FanoutCoherent source replica state)
    (redirect : Bool) {action : Act}
    (freshRead : action.readsReg replica = false)
    (freshWrite : action.writesReg replica = false)
    {impl spec : St} (related : FanoutRel source replica impl spec) :
    FanoutRel source replica
      ((action.duplicateFanoutAct source replica redirect).run state impl)
      (action.run (fanoutAbs replica state) spec) := by
  induction action generalizing impl spec with
  | skip => exact related
  | seq first second ihFirst ihSecond =>
      simp only [Act.readsReg, Bool.or_eq_false_iff] at freshRead
      simp only [Act.writesReg, Bool.or_eq_false_iff] at freshWrite
      exact ihSecond freshRead.2 freshWrite.2
        (ihFirst freshRead.1 freshWrite.1 related)
  | ite cond yes no ihYes ihNo =>
      simp only [Act.readsReg, Bool.or_eq_false_iff] at freshRead
      simp only [Act.writesReg, Bool.or_eq_false_iff] at freshWrite
      simp only [Act.duplicateFanoutAct, Act.run]
      rw [cond.eval_redirectIf source replica state hne stateCoherent redirect freshRead.1.1]
      by_cases condition : cond.eval (fanoutAbs replica state) = 1#1
      · rw [if_pos condition, if_pos condition]
        exact ihYes freshRead.1.2 freshWrite.1 related
      · rw [if_neg condition, if_neg condition]
        exact ihNo freshRead.2 freshWrite.2 related
  | write valueWidth target value =>
      simp only [Act.readsReg] at freshRead
      simp only [Act.writesReg, beq_eq_false_iff_ne, ne_eq] at freshWrite
      have valueEq := value.eval_redirectIf source replica state hne stateCoherent
        redirect freshRead
      simp only [Act.duplicateFanoutAct]
      by_cases targetSource : target = source
      · rw [if_pos targetSource]
        subst targetSource
        simp only [Act.run]
        rw [valueEq]
        refine ⟨?_, ?_, ?_, related.mems⟩
        · intro name width nameReplica
          change ((impl.regs.set target _).set replica _) name width =
            (spec.regs.set target _) name width
          rw [RegEnv.set_get_ne _ _ _ _ _ nameReplica]
          by_cases nameSource : name = target
          · subst nameSource
            by_cases widths : valueWidth = width
            · subst widths
              rw [RegEnv.set_get_eq, RegEnv.set_get_eq]
            · rw [RegEnv.set_get_same _ _ _ _ widths,
                  RegEnv.set_get_same _ _ _ _ widths]
              exact related.regs name width hne
          · rw [RegEnv.set_get_ne _ _ _ _ _ nameSource,
                RegEnv.set_get_ne _ _ _ _ _ nameSource]
            exact related.regs name width nameReplica
        · intro width
          change ((impl.regs.set target _).set replica _) target width =
            ((impl.regs.set target _).set replica _) replica width
          rw [RegEnv.set_get_ne _ _ _ _ _ hne]
          by_cases widths : valueWidth = width
          · subst widths
            rw [RegEnv.set_get_eq, RegEnv.set_get_eq]
          · rw [RegEnv.set_get_same _ _ _ _ widths,
                RegEnv.set_get_same _ _ _ _ widths,
                RegEnv.set_get_ne _ _ _ _ _ (Ne.symm hne)]
            exact related.coherent width
        · intro width
          change (spec.regs.set target _) replica width = 0#width
          rw [RegEnv.set_get_ne _ _ _ _ _ (Ne.symm hne)]
          exact related.spec_replica width
      · rw [if_neg targetSource]
        simp only [Act.run]
        rw [valueEq]
        have targetReplica : target ≠ replica := freshWrite
        refine ⟨?_, ?_, ?_, related.mems⟩
        · intro name width nameReplica
          change (impl.regs.set target _) name width =
            (spec.regs.set target _) name width
          by_cases nameTarget : name = target
          · subst nameTarget
            by_cases widths : valueWidth = width
            · subst widths
              rw [RegEnv.set_get_eq, RegEnv.set_get_eq]
            · rw [RegEnv.set_get_same _ _ _ _ widths,
                  RegEnv.set_get_same _ _ _ _ widths]
              exact related.regs name width targetReplica
          · rw [RegEnv.set_get_ne _ _ _ _ _ nameTarget,
                RegEnv.set_get_ne _ _ _ _ _ nameTarget]
            exact related.regs name width nameReplica
        · intro width
          change (impl.regs.set target _) source width =
            (impl.regs.set target _) replica width
          rw [RegEnv.set_get_ne _ _ _ _ _ (Ne.symm targetSource),
              RegEnv.set_get_ne _ _ _ _ _ (Ne.symm targetReplica)]
          exact related.coherent width
        · intro width
          change (spec.regs.set target _) replica width = 0#width
          rw [RegEnv.set_get_ne _ _ _ _ _ (Ne.symm targetReplica)]
          exact related.spec_replica width
  | writeSlice valueWidth target lo fieldWidth inBounds value =>
      simp only [Act.readsReg] at freshRead
      simp only [Act.writesReg, beq_eq_false_iff_ne, ne_eq] at freshWrite
      have valueEq := value.eval_redirectIf source replica state hne stateCoherent
        redirect freshRead
      simp only [Act.duplicateFanoutAct]
      by_cases targetSource : target = source
      · rw [if_pos targetSource]
        subst targetSource
        simp only [Act.run]
        rw [valueEq]
        have mergeSource :
            Loom.Word.insert lo (value.eval (fanoutAbs replica state))
                (impl.regs target valueWidth) =
              Loom.Word.insert lo (value.eval (fanoutAbs replica state))
                (spec.regs target valueWidth) := by
          rw [related.regs target valueWidth hne]
        have mergeReplica :
            Loom.Word.insert lo (value.eval (fanoutAbs replica state))
                (impl.regs replica valueWidth) =
              Loom.Word.insert lo (value.eval (fanoutAbs replica state))
                (spec.regs target valueWidth) := by
          rw [← related.coherent valueWidth,
            related.regs target valueWidth hne]
        rw [mergeSource,
          RegEnv.set_get_ne _ _ _ _ _ (Ne.symm hne), mergeReplica]
        refine ⟨?_, ?_, ?_, related.mems⟩
        · intro name width nameReplica
          change ((impl.regs.set target _).set replica _) name width =
            (spec.regs.set target _) name width
          rw [RegEnv.set_get_ne _ _ _ _ _ nameReplica]
          by_cases nameSource : name = target
          · subst nameSource
            by_cases widths : valueWidth = width
            · subst widths; rw [RegEnv.set_get_eq, RegEnv.set_get_eq]
            · rw [RegEnv.set_get_same _ _ _ _ widths,
                RegEnv.set_get_same _ _ _ _ widths]
              exact related.regs name width hne
          · rw [RegEnv.set_get_ne _ _ _ _ _ nameSource,
              RegEnv.set_get_ne _ _ _ _ _ nameSource]
            exact related.regs name width nameReplica
        · intro width
          change ((impl.regs.set target _).set replica _) target width =
            ((impl.regs.set target _).set replica _) replica width
          rw [RegEnv.set_get_ne _ _ _ _ _ hne]
          by_cases widths : valueWidth = width
          · subst widths; rw [RegEnv.set_get_eq, RegEnv.set_get_eq]
          · rw [RegEnv.set_get_same _ _ _ _ widths,
              RegEnv.set_get_same _ _ _ _ widths,
              RegEnv.set_get_ne _ _ _ _ _ (Ne.symm hne)]
            exact related.coherent width
        · intro width
          change (spec.regs.set target _) replica width = 0#width
          rw [RegEnv.set_get_ne _ _ _ _ _ (Ne.symm hne)]
          exact related.spec_replica width
      · rw [if_neg targetSource]
        simp only [Act.run]
        rw [valueEq]
        have targetReplica : target ≠ replica := freshWrite
        have mergeTarget :
            Loom.Word.insert lo (value.eval (fanoutAbs replica state))
                (impl.regs target valueWidth) =
              Loom.Word.insert lo (value.eval (fanoutAbs replica state))
                (spec.regs target valueWidth) := by
          rw [related.regs target valueWidth targetReplica]
        rw [mergeTarget]
        refine ⟨?_, ?_, ?_, related.mems⟩
        · intro name width nameReplica
          change (impl.regs.set target _) name width =
            (spec.regs.set target _) name width
          by_cases nameTarget : name = target
          · subst nameTarget
            by_cases widths : valueWidth = width
            · subst widths; rw [RegEnv.set_get_eq, RegEnv.set_get_eq]
            · rw [RegEnv.set_get_same _ _ _ _ widths,
                RegEnv.set_get_same _ _ _ _ widths]
              exact related.regs name width targetReplica
          · rw [RegEnv.set_get_ne _ _ _ _ _ nameTarget,
              RegEnv.set_get_ne _ _ _ _ _ nameTarget]
            exact related.regs name width nameReplica
        · intro width
          change (impl.regs.set target _) source width =
            (impl.regs.set target _) replica width
          rw [RegEnv.set_get_ne _ _ _ _ _ (Ne.symm targetSource),
            RegEnv.set_get_ne _ _ _ _ _ (Ne.symm targetReplica)]
          exact related.coherent width
        · intro width
          change (spec.regs.set target _) replica width = 0#width
          rw [RegEnv.set_get_ne _ _ _ _ _ (Ne.symm targetReplica)]
          exact related.spec_replica width
  | memWrite addressWidth dataWidth memory port address data =>
      simp only [Act.readsReg, Bool.or_eq_false_iff] at freshRead
      have addressEq := address.eval_redirectIf source replica state hne stateCoherent
        redirect freshRead.1
      have dataEq := data.eval_redirectIf source replica state hne stateCoherent
        redirect freshRead.2
      simp only [Act.duplicateFanoutAct, Act.run]
      rw [addressEq, dataEq]
      refine ⟨related.regs, related.coherent, related.spec_replica, ?_⟩
      rw [related.mems]

/-- A coherent state and its abstraction form the initial accumulator
relation for a transformed cycle. -/
theorem FanoutRel.initial (source replica : String) (state : St)
    (coherent : FanoutCoherent source replica state) :
    FanoutRel source replica state (fanoutAbs replica state) := by
  refine ⟨?_, coherent, ?_, rfl⟩
  · intro name width fresh
    simp [fanoutAbs, fresh]
  · intro width
    simp [fanoutAbs]

/-- Folding any list of fresh rules preserves the fan-out relation. -/
theorem FanoutRel.fold_duplicate (source replica : String) (hne : source ≠ replica)
    (state : St) (stateCoherent : FanoutCoherent source replica state)
    (consumers : List String) (rules : List Rule)
    (freshRead : ∀ rule ∈ rules, rule.body.readsReg replica = false)
    (freshWrite : ∀ rule ∈ rules, rule.body.writesReg replica = false)
    {impl spec : St} (related : FanoutRel source replica impl spec) :
    FanoutRel source replica
      ((rules.map fun rule => { rule with body :=
          (rule.body.duplicateFanoutAct source replica (consumers.contains rule.name)) }).foldl
        (fun acc rule => rule.body.run state acc) impl)
      (rules.foldl (fun acc rule => rule.body.run (fanoutAbs replica state) acc) spec) := by
  induction rules generalizing impl spec with
  | nil => exact related
  | cons head tail ih =>
      simp only [List.map_cons, List.foldl_cons]
      exact ih
        (fun rule member => freshRead rule (List.mem_cons_of_mem head member))
        (fun rule member => freshWrite rule (List.mem_cons_of_mem head member))
        (related.run_duplicate source replica hne state stateCoherent
          (consumers.contains head.name)
          (freshRead head (List.mem_cons_self ..))
          (freshWrite head (List.mem_cons_self ..)))

/-- A related implementation accumulator abstracts exactly to the source
accumulator. -/
theorem FanoutRel.abs_eq {source replica : String} {impl spec : St}
    (related : FanoutRel source replica impl spec) :
    fanoutAbs replica impl = spec := by
  apply St.mk.injEq _ _ _ _ |>.mpr
  refine ⟨?_, related.mems⟩
  funext name width
  by_cases fresh : name = replica
  · subst fresh
    simp [related.spec_replica]
  · simp [fresh, related.regs name width fresh]

/-! ## Legality, reset, and the proof-carrying transform -/

/-- Propositional legality bundle for the verified duplication theorem. -/
structure FanoutLegal (design : Design) (source : String) (width : Nat)
    (replica : String := fanoutName source) : Prop where
  decl : (⟨source, width, retimeRegInit design source width⟩ : RegDecl) ∈ design.regs
  nodup : (design.regs.map (·.name)).Nodup
  freshReg : ∀ decl ∈ design.regs, decl.name ≠ replica
  freshInput : ∀ input ∈ design.inputs, input.name ≠ replica
  freshMem : ∀ memory ∈ design.mems, memory.name ≠ replica
  distinct : source ≠ replica
  noReadReplica : design.readsReg replica = false
  noWriteReplica : design.writesReg replica = false

/-- The facts represented by `duplicateFanoutOkB`, stated independently of
the Boolean encoding for diagnostics and downstream proofs. -/
theorem duplicateFanoutOkB_facts (design : Design) (source : String) (width : Nat)
    (replica : String) (checked : duplicateFanoutOkB design source width replica = true) :
    (design.regs.map (·.name)).Nodup ∧
    (∃ decl ∈ design.regs, decl.name = source ∧ decl.width = width) ∧
    (∀ decl ∈ design.regs, decl.name ≠ replica) ∧
    (∀ input ∈ design.inputs, input.name ≠ replica) ∧
    (∀ memory ∈ design.mems, memory.name ≠ replica) ∧
    design.readsReg replica = false ∧
    design.writesReg replica = false ∧
    source ≠ replica := by
  simp only [duplicateFanoutOkB, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.any_eq_false, beq_iff_eq,
    Bool.not_eq_true', bne_iff_ne, ne_eq] at checked
  obtain ⟨⟨⟨⟨⟨⟨⟨nodup, existsDecl⟩, freshReg⟩, freshInput⟩, freshMem⟩,
      noRead⟩, noWrite⟩, distinct⟩ := checked
  exact ⟨nodup, existsDecl, freshReg, freshInput, freshMem,
    noRead, noWrite, distinct⟩

/-- A unique matching source declaration supplies the exact initialization
record used by `retimeRegInit`. -/
private theorem retimeRegInit_decl (design : Design) (source : String) (width : Nat)
    (nodup : (design.regs.map (·.name)).Nodup)
    (existsDecl : ∃ decl ∈ design.regs,
      decl.name = source ∧ decl.width = width) :
    (⟨source, width, retimeRegInit design source width⟩ : RegDecl) ∈ design.regs := by
  obtain ⟨decl, member, nameEq, widthEq⟩ := existsDecl
  obtain ⟨declName, declWidth, declInit⟩ := decl
  change declName = source at nameEq
  change declWidth = width at widthEq
  subst declName
  subst declWidth
  have initEq : retimeRegInit design source width = declInit := by
    unfold retimeRegInit
    generalize foundEq : design.regs.find? (fun rd => rd.name = source) = found
    cases found with
    | none =>
        have absent := List.find?_eq_none.mp foundEq
          ⟨source, width, declInit⟩ member
        simp at absent
    | some foundDecl =>
        have foundMember := List.mem_of_find?_eq_some foundEq
        have foundName := List.find?_some foundEq
        have unique : foundDecl = ⟨source, width, declInit⟩ :=
          regName_unique design.regs nodup foundDecl ⟨source, width, declInit⟩
            foundMember member (by simpa using foundName)
        subst foundDecl
        simp
  simpa [initEq] using member

/-- Acceptance of the executable guard constructs exactly the legality
witness required by the coherence and refinement theorems. -/
theorem duplicateFanoutOkB_sound (design : Design) (source : String) (width : Nat)
    (replica : String) (checked : duplicateFanoutOkB design source width replica = true) :
    FanoutLegal design source width replica := by
  obtain ⟨nodup, existsDecl, freshReg, freshInput, freshMem,
      noRead, noWrite, distinct⟩ :=
    duplicateFanoutOkB_facts design source width replica checked
  exact
    { decl := retimeRegInit_decl design source width nodup existsDecl
      nodup := nodup
      freshReg := freshReg
      freshInput := freshInput
      freshMem := freshMem
      distinct := distinct
      noReadReplica := noRead
      noWriteReplica := noWrite }

/-- Typed form of `duplicateFanoutOkB_sound`. -/
theorem duplicateFanoutRegOkB_sound {width : Nat} (design : Design)
    (source : Reg width) (replica : String)
    (checked : duplicateFanoutRegOkB design source replica = true) :
    FanoutLegal design source.name width replica :=
  duplicateFanoutOkB_sound design source.name width replica checked

/-- Reset lookup after appending the replica declaration. -/
private theorem duplicateFanout_reset_get (design : Design) (source : String)
    (width : Nat) (replica : String) (consumers : List String)
    (name : String) (readWidth : Nat) :
    (duplicateFanout design source width replica consumers).reset.regs name readWidth =
      if _hn : name = replica then
        (if hw : width = readWidth then hw ▸ retimeRegInit design source width
         else design.reset.regs name readWidth)
      else design.reset.regs name readWidth := by
  exact foldl_reset_append_pre design.regs (fun _ w => 0#w)
    ⟨replica, width, retimeRegInit design source width⟩ name readWidth

/-- Erasing the fresh reset coordinate reproduces the source reset. -/
theorem duplicateFanout_reset_abs (design : Design) (source : String) (width : Nat)
    (replica : String) (consumers : List String)
    (legal : FanoutLegal design source width replica) :
    fanoutAbs replica (duplicateFanout design source width replica consumers).reset =
      design.reset := by
  apply St.mk.injEq _ _ _ _ |>.mpr
  refine ⟨?_, rfl⟩
  funext name readWidth
  by_cases nameReplica : name = replica
  · subst nameReplica
    simp only [if_pos]
    exact (design.reset_regs_notMem name readWidth legal.freshReg).symm
  · simp only [if_neg nameReplica]
    rw [duplicateFanout_reset_get]
    simp only [dif_neg nameReplica]
    rfl

/-- Source and replica reset to the same value at every width. -/
theorem duplicateFanout_reset_coherent (design : Design) (source : String)
    (width : Nat) (replica : String) (consumers : List String)
    (legal : FanoutLegal design source width replica) :
    FanoutCoherent source replica
      (duplicateFanout design source width replica consumers).reset := by
  intro readWidth
  rw [duplicateFanout_reset_get, duplicateFanout_reset_get]
  simp only [dif_neg legal.distinct]
  by_cases widths : width = readWidth
  · subst readWidth
    rw [dif_pos rfl]
    exact foldl_reset_get design.regs _
      ⟨source, width, retimeRegInit design source width⟩ legal.decl legal.nodup
  · rw [dif_neg widths]
    rw [design.reset_regs_notMem replica readWidth legal.freshReg]
    have sourceWrongWidth : ∀ decl ∈ design.regs,
        decl.name = source → decl.width ≠ readWidth := by
      intro decl member sameName
      have unique : decl = ⟨source, width, retimeRegInit design source width⟩ :=
        regName_unique design.regs legal.nodup decl
          ⟨source, width, retimeRegInit design source width⟩ member legal.decl
          (by rw [sameName])
      rw [unique]
      exact widths
    rw [design.reset_regs_noWidth source readWidth sourceWrongWidth]
    simp

/-- One coherent implementation cycle both preserves coherence and commutes
with the source cycle after erasing the replica. -/
theorem duplicateFanout_cycle (design : Design) (source replica : String)
    (width : Nat) (consumers : List String)
    (distinct : source ≠ replica)
    (noReadReplica : design.readsReg replica = false)
    (noWriteReplica : design.writesReg replica = false)
    (state : St) (coherent : FanoutCoherent source replica state) :
    fanoutAbs replica
        ((duplicateFanout design source width replica consumers).cycle state) =
        design.cycle (fanoutAbs replica state) ∧
      FanoutCoherent source replica
        ((duplicateFanout design source width replica consumers).cycle state) := by
  have freshRead : ∀ rule ∈ design.rules, rule.body.readsReg replica = false := by
    intro rule member
    have fresh := (List.any_eq_false.mp noReadReplica) rule member
    simpa using fresh
  have freshWrite : ∀ rule ∈ design.rules, rule.body.writesReg replica = false := by
    intro rule member
    have fresh := (List.any_eq_false.mp noWriteReplica) rule member
    simpa using fresh
  have related := FanoutRel.fold_duplicate source replica distinct state coherent
    consumers design.rules freshRead freshWrite
    (FanoutRel.initial source replica state coherent)
  have cycleRelated : FanoutRel source replica
      ((duplicateFanout design source width replica consumers).cycle state)
      (design.cycle (fanoutAbs replica state)) := by
    simpa [duplicateFanout, Design.cycle] using related
  exact ⟨cycleRelated.abs_eq, cycleRelated.coherent⟩

/-- Replica coherence is an invariant of the transformed machine. -/
theorem duplicateFanout_coherent_invariant (design : Design) (source : String)
    (width : Nat) (replica : String) (consumers : List String)
    (legal : FanoutLegal design source width replica) :
    (duplicateFanout design source width replica consumers).toTSys.Invariant
      (FanoutCoherent source replica) := by
  apply Loom.TSys.Inductive.invariant
  constructor
  · intro state initial
    have : state = (duplicateFanout design source width replica consumers).reset := initial
    subst state
    exact duplicateFanout_reset_coherent design source width replica consumers legal
  · intro state next stateCoherent step
    have cycleNext :
        (duplicateFanout design source width replica consumers).cycle state = next := step
    subst next
    exact (duplicateFanout_cycle design source replica width consumers legal.distinct
      legal.noReadReplica legal.noWriteReplica state stateCoherent).2

/-- The duplicated design refines the source on its powered-on state space.
The restriction is semantically necessary: an arbitrary hand-constructed
concrete state may give the two copies different values. -/
def duplicateFanout_simulation (design : Design) (source : String) (width : Nat)
    (replica : String) (consumers : List String)
    (legal : FanoutLegal design source width replica) :
    Loom.Simulation design.toTSys
      (duplicateFanout design source width replica consumers).toTSys.reachablePart where
  abs := fanoutAbs replica
  init_ok := by
    intro state initial
    have : state = (duplicateFanout design source width replica consumers).reset := initial
    subst state
    exact duplicateFanout_reset_abs design source width replica consumers legal
  square := by
    intro state next transition
    have coherent := duplicateFanout_coherent_invariant design source width replica consumers
      legal state transition.1
    have cycleNext :
        (duplicateFanout design source width replica consumers).cycle state = next := transition.2
    show design.cycle (fanoutAbs replica state) = fanoutAbs replica next
    rw [← cycleNext]
    exact (duplicateFanout_cycle design source replica width consumers legal.distinct
      legal.noReadReplica legal.noWriteReplica state coherent).1.symm

/-- Transport a source invariant to the ordinary (unrestricted presentation
of the) duplicated design. Reachability supplies replica coherence. -/
theorem duplicateFanout_invariant_pullback (design : Design) (source : String)
    (width : Nat) (replica : String) (consumers : List String)
    (legal : FanoutLegal design source width replica) {property : St → Prop}
    (invariant : design.toTSys.Invariant property) :
    (duplicateFanout design source width replica consumers).toTSys.Invariant
      (fun state => property (fanoutAbs replica state)) :=
  Loom.Simulation.invariant_pullback_reachablePart
    (duplicateFanout_simulation design source width replica consumers legal) invariant

end Loom.Hw
