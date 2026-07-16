-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.RoundTrip

/-!
# Kernel-checkable release-artifact certificates

The executable compiler and printer are deliberately optimized with private
unsafe implementations. Release artifacts therefore need a proof-producing
validation path that checks supplied results locally, without evaluating the
large reference compiler/printer output as a whole.

This module builds that validator bottom-up. `compileExprMatches` is the
expression layer: it walks a source EDSL expression and a supplied µVerilog
expression in lockstep. Its soundness theorem recovers equality with the
reference `Compile.compileExpr`, while the Boolean checker never constructs
that reference result. Register-fold, memory-port, module, and text-certificate
layers build on this primitive.
-/

namespace Loom.Hw.ArtifactCert

open Loom.Hw
open Loom.Emit.MicroVerilog

/-- Locally check that a supplied µVerilog expression is the structural
translation of an EDSL expression. Unlike deciding equality with
`Compile.compileExpr e`, this does not first materialize the reference result. -/
def compileExprMatches : {w : Nat} → Loom.Hw.Expr w →
    Loom.Emit.MicroVerilog.Expr w → Bool
  | _, .lit a, .lit b => decide (a = b)
  | _, .reg _ na, .reg _ nb => decide (na = nb)
  | _, @Loom.Hw.Expr.memRead _ ma awa aa,
      @Loom.Emit.MicroVerilog.Expr.memRead _ mb awb ab =>
      decide (ma = mb) &&
        if h : awa = awb then compileExprMatches aa (h ▸ ab) else false
  | _, .and aa ba, .and ab bb
  | _, .or aa ba, .or ab bb
  | _, .xor aa ba, .xor ab bb
  | _, .add aa ba, .add ab bb
  | _, .sub aa ba, .sub ab bb
  | _, .shl aa ba, .shl ab bb
  | _, .shr aa ba, .shr ab bb =>
      compileExprMatches aa ab && compileExprMatches ba bb
  | _, @Loom.Hw.Expr.eq wa aa ba,
      @Loom.Emit.MicroVerilog.Expr.eq wb ab bb
  | _, @Loom.Hw.Expr.ult wa aa ba,
      @Loom.Emit.MicroVerilog.Expr.ult wb ab bb
  | _, @Loom.Hw.Expr.slt wa aa ba,
      @Loom.Emit.MicroVerilog.Expr.slt wb ab bb =>
      if h : wa = wb then
        compileExprMatches aa (h ▸ ab) && compileExprMatches ba (h ▸ bb)
      else false
  | _, .not a, .not b => compileExprMatches a b
  | _, .mux ca ta fa, .mux cb tb fb =>
      compileExprMatches ca cb && compileExprMatches ta tb &&
        compileExprMatches fa fb
  | _, @Loom.Hw.Expr.slice wa a loa _,
      @Loom.Emit.MicroVerilog.Expr.slice wb b lob _ =>
      decide (loa = lob) &&
        if h : wa = wb then compileExprMatches a (h ▸ b) else false
  | _, @Loom.Hw.Expr.zext wa a _,
      @Loom.Emit.MicroVerilog.Expr.zext wb b _
  | _, @Loom.Hw.Expr.sext wa a _,
      @Loom.Emit.MicroVerilog.Expr.sext wb b _ =>
      if h : wa = wb then compileExprMatches a (h ▸ b) else false
  | _, _, _ => false

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- A successful local expression check identifies the supplied expression
with the reference compiler's structural translation. -/
theorem compileExprMatches_sound : ∀ {w : Nat} (a : Loom.Hw.Expr w)
    (b : Loom.Emit.MicroVerilog.Expr w),
    compileExprMatches a b = true → b = Compile.compileExpr a := by
  intro w a
  induction a <;> intro b h <;> cases b <;>
    simp only [compileExprMatches, Bool.and_eq_true, decide_eq_true_eq] at h <;>
    simp only [Compile.compileExpr] <;>
    grind

/-! ## Register-fold certificates -/

/-- Proof data for one `Compile.nextReg` fold. Sequential actions expose
their intermediate expression; guarded actions carry certificates for both
branches. Leaf constructors distinguish preservation from an actual write,
making malformed certificate shapes reject definitionally. -/
inductive NextRegCert (w : Nat) where
  | same
  | write
  | seq (mid : Loom.Emit.MicroVerilog.Expr w)
      (left right : NextRegCert w)
  | ite (thenCert elseCert : NextRegCert w)

private theorem nextReg_eq_of_no_write (rn : String) (w : Nat) :
    ∀ (a : Loom.Hw.Act) (cur : Loom.Emit.MicroVerilog.Expr w),
      Compile.writesRegB rn w a = false → Compile.nextReg rn w a cur = cur := by
  intro a
  induction a with
  | skip => intro _ _; rfl
  | seq left right ihLeft ihRight =>
      intro cur h
      have hn : (rn, w) ∉ (left.seq right).regWrites := by
        simpa [Compile.writesRegB] using h
      simp only [Loom.Hw.Act.regWrites, List.mem_append, not_or] at hn
      rw [Compile.nextReg,
        ihRight _ (by simpa [Compile.writesRegB] using hn.2),
        ihLeft _ (by simpa [Compile.writesRegB] using hn.1)]
  | ite guard thenAct elseAct ihThen ihElse =>
      intro cur h
      have hn : (rn, w) ∉ (Loom.Hw.Act.ite guard thenAct elseAct).regWrites := by
        simpa [Compile.writesRegB] using h
      simp only [Loom.Hw.Act.regWrites, List.mem_append, not_or] at hn
      rw [Compile.nextReg, if_neg]
      simp [Compile.writesRegB, hn]
  | write actualWidth name value =>
      intro cur h
      have hn : (rn, w) ∉ (Loom.Hw.Act.write actualWidth name value).regWrites := by
        simpa [Compile.writesRegB] using h
      simp only [Compile.nextReg]
      by_cases hname : name = rn
      · rw [if_pos hname]
        have hwidth : actualWidth ≠ w := by
          intro hw
          exact hn (by simp [Loom.Hw.Act.regWrites, hname, hw])
        rw [dif_neg hwidth]
      · rw [if_neg hname]
  | memWrite => intro _ _; rfl

/-- Check a supplied result of one `nextReg` action locally. -/
def nextRegMatches (rn : String) (w : Nat) : Loom.Hw.Act →
    Loom.Emit.MicroVerilog.Expr w → Loom.Emit.MicroVerilog.Expr w →
    NextRegCert w → Bool
  | .skip, cur, out, .same => decide (out = cur)
  | .seq a b, cur, out, .seq mid ca cb =>
      nextRegMatches rn w a cur mid ca &&
        nextRegMatches rn w b mid out cb
  | .seq a b, cur, out, .same =>
      if Compile.writesRegB rn w (.seq a b) then false else decide (out = cur)
  | .ite c t e, cur, out, .ite ct ce =>
      if Compile.writesRegB rn w t || Compile.writesRegB rn w e then
        match out with
        | .mux g ot oe =>
            compileExprMatches c g && nextRegMatches rn w t cur ot ct &&
              nextRegMatches rn w e cur oe ce
        | _ => false
      else false
  | .ite _c t e, cur, out, .same =>
      if Compile.writesRegB rn w t || Compile.writesRegB rn w e then false
      else decide (out = cur)
  | .write w' r' v, cur, out, cert =>
      if _hr : r' = rn then
        if hw : w' = w then
          match cert with
          | .write => compileExprMatches (hw ▸ v) out
          | _ => false
        else
          match cert with
          | .same => decide (out = cur)
          | _ => false
      else
        match cert with
        | .same => decide (out = cur)
        | _ => false
  | .memWrite .., cur, out, .same => decide (out = cur)
  | _, _, _, _ => false

/-- A successful register-fold certificate recovers equality with the
reference `nextReg` result. -/
theorem nextRegMatches_sound (rn : String) (w : Nat) :
    ∀ (a : Loom.Hw.Act) (cur out : Loom.Emit.MicroVerilog.Expr w)
      (cert : NextRegCert w),
      nextRegMatches rn w a cur out cert = true →
        out = Compile.nextReg rn w a cur := by
  intro a
  induction a <;> intro cur out cert h
  · cases cert <;>
      simp only [nextRegMatches] at h <;>
      simp_all [Compile.nextReg]
  · rename_i a b iha ihb
    cases cert with
    | seq mid ca cb =>
        simp only [nextRegMatches, Bool.and_eq_true] at h
        rw [Compile.nextReg]
        rw [ihb mid out cb h.2, iha cur mid ca h.1]
    | same =>
        simp only [nextRegMatches] at h
        split at h
        · contradiction
        · rename_i hn
          simp only [decide_eq_true_eq] at h
          rw [h, nextReg_eq_of_no_write rn w (.seq a b) cur (by simpa using hn)]
    | _ => simp [nextRegMatches] at h
  · rename_i c t e iht ihe
    by_cases hwrites : Compile.writesRegB rn w t ||
        Compile.writesRegB rn w e
    · cases cert with
      | ite ct ce =>
          cases out <;> simp [nextRegMatches, hwrites] at h
          rename_i g ot oe
          obtain ⟨⟨hg, ht⟩, he⟩ := h
          rw [Compile.nextReg, if_pos hwrites,
            compileExprMatches_sound c g hg,
            iht cur ot ct ht, ihe cur oe ce he]
      | _ => simp [nextRegMatches, hwrites] at h
    · cases cert <;> simp [nextRegMatches, Compile.nextReg, hwrites] at h ⊢
      exact h
  · rename_i w' r' v
    by_cases hr : r' = rn
    · by_cases hw : w' = w
      · subst r'; subst w'
        cases cert <;> simp [nextRegMatches, Compile.nextReg] at h ⊢
        exact compileExprMatches_sound v out h
      · cases cert <;> simp [nextRegMatches, Compile.nextReg, hr, hw] at h ⊢
        exact h
    · cases cert <;> simp [nextRegMatches, Compile.nextReg, hr] at h ⊢
      exact h
  · cases cert <;> simp [nextRegMatches, Compile.nextReg] at h ⊢
    exact h

/-- Proof data for folding an ordered rule list. Each entry supplies the
post-rule intermediate expression and the local action certificate. -/
inductive NextRulesCert (w : Nat) where
  | nil
  | cons (mid : Loom.Emit.MicroVerilog.Expr w) (head : NextRegCert w)
      (tail : NextRulesCert w)

/-- Check an entire ordered register-rule fold without constructing the
reference `List.foldl` result. -/
def nextRulesMatches (rn : String) (w : Nat) : List Loom.Hw.Rule →
    Loom.Emit.MicroVerilog.Expr w → Loom.Emit.MicroVerilog.Expr w →
    NextRulesCert w → Bool
  | [], cur, out, .nil => decide (out = cur)
  | rl :: rls, cur, out, .cons mid ch ct =>
      nextRegMatches rn w rl.body cur mid ch &&
        nextRulesMatches rn w rls mid out ct
  | _, _, _, _ => false

/-- A successful rule-fold certificate recovers the reference fold used in
the register definition produced by `Compile.compile`. -/
theorem nextRulesMatches_sound (rn : String) (w : Nat) :
    ∀ (rules : List Loom.Hw.Rule)
      (cur out : Loom.Emit.MicroVerilog.Expr w) (cert : NextRulesCert w),
      nextRulesMatches rn w rules cur out cert = true →
        out = rules.foldl
          (fun acc rl => Compile.nextReg rn w rl.body acc) cur := by
  intro rules
  induction rules with
  | nil =>
      intro cur out cert h
      cases cert <;> simp [nextRulesMatches] at h ⊢
      exact h
  | cons rl rls ih =>
      intro cur out cert h
      cases cert with
      | cons mid ch ct =>
          simp only [nextRulesMatches, Bool.and_eq_true] at h
          simp only [List.foldl_cons]
          rw [ih mid out ct h.2, nextRegMatches_sound rn w rl.body cur mid ch h.1]
      | _ => simp [nextRulesMatches] at h

/-! ## Register-list certificates -/

/-- Certificate for the compiled definition of one source register. -/
structure RegCert (r : Loom.Hw.RegDecl) where
  rules : NextRulesCert r.width

/-- Check one supplied register definition against its source declaration
and the design's ordered rule list. -/
def regMatches (rules : List Loom.Hw.Rule) (r : Loom.Hw.RegDecl)
    (out : Loom.Emit.MicroVerilog.RegDef) (cert : RegCert r) : Bool :=
  decide (out.name = r.name) &&
  if h : out.width = r.width then
    decide (h ▸ out.init = r.init) &&
      nextRulesMatches r.name r.width rules (.reg r.width r.name)
        (h ▸ out.next) cert.rules
  else false

/-- A successful register certificate recovers the exact reference
`RegDef` produced by `Compile.compile`. -/
theorem regMatches_sound (rules : List Loom.Hw.Rule) (r : Loom.Hw.RegDecl)
    (out : Loom.Emit.MicroVerilog.RegDef) (cert : RegCert r)
    (h : regMatches rules r out cert = true) :
    out = ({ name := r.name, width := r.width, init := r.init,
             next := rules.foldl
               (fun cur rl => Compile.nextReg r.name r.width rl.body cur)
               (.reg r.width r.name) } : Loom.Emit.MicroVerilog.RegDef) := by
  unfold regMatches at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hrest⟩ := h
  split at hrest
  · rename_i hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
    obtain ⟨hi, hnxt⟩ := hrest
    have hout := nextRulesMatches_sound r.name r.width rules
      (.reg r.width r.name) (hw ▸ out.next) cert.rules hnxt
    cases r
    cases out
    simp at hn hw hi hout ⊢
    cases hn
    cases hw
    cases hi
    cases hout
    simp
  · contradiction

/-- A dependent certificate list aligned with the source register list. -/
inductive RegsCert : List Loom.Hw.RegDecl → Type where
  | nil : RegsCert []
  | cons {r rs} (head : RegCert r) (tail : RegsCert rs) : RegsCert (r :: rs)

/-- Check all supplied register definitions in declaration order. -/
def regsMatch (rules : List Loom.Hw.Rule) :
    ∀ {rs : List Loom.Hw.RegDecl}, List Loom.Emit.MicroVerilog.RegDef →
      RegsCert rs → Bool
  | [], [], .nil => true
  | _ :: _, [], .cons _ _ => false
  | [], _ :: _, .nil => false
  | r :: _, out :: outs, .cons ch ct =>
      regMatches rules r out ch && regsMatch rules outs ct

/-- Successful register-list validation recovers the reference compiler's
entire register list. -/
theorem regsMatch_sound (rules : List Loom.Hw.Rule) :
    ∀ {rs : List Loom.Hw.RegDecl} (outs : List Loom.Emit.MicroVerilog.RegDef)
      (cert : RegsCert rs),
      regsMatch rules outs cert = true →
      outs = rs.map fun r =>
        ({ name := r.name, width := r.width, init := r.init,
           next := rules.foldl
             (fun cur rl => Compile.nextReg r.name r.width rl.body cur)
             (.reg r.width r.name) } : Loom.Emit.MicroVerilog.RegDef)
  | [], [], .nil, _ => rfl
  | [], _ :: _, .nil, h => by simp [regsMatch] at h
  | _ :: _, [], .cons _ _, h => by simp [regsMatch] at h
  | r :: rs, out :: outs, .cons ch ct, h => by
      simp only [regsMatch, Bool.and_eq_true] at h
      simp only [List.map_cons]
      rw [regMatches_sound rules r out ch h.1,
        regsMatch_sound rules outs ct h.2]

/-! ## Memory-port certificates -/

/-- Proof data for one `Compile.memPort` fold. Intermediate ports make the
sequential and conditional structure explicit while expression leaves are
checked by `compileExprMatches`. -/
inductive NextPortCert (aw dw : Nat) where
  | same
  | write
  | seq (mid : Compile.Port aw dw) (left right : NextPortCert aw dw)
  | ite (guard : Loom.Emit.MicroVerilog.Expr 1)
      (thenPort elsePort : Compile.Port aw dw)
      (thenCert elseCert : NextPortCert aw dw)

private theorem memPort_eq_of_no_write (mn : String) (aw dw p : Nat) :
    ∀ (a : Loom.Hw.Act) (cur : Compile.Port aw dw),
      Compile.writesPortB mn p a = false →
        Compile.memPort mn aw dw p a cur = cur := by
  intro a
  induction a with
  | skip => intro _ _; rfl
  | seq left right ihLeft ihRight =>
      intro cur h
      have hn : p ∉ Compile.portTrace mn (left.seq right) := by
        simpa [Compile.writesPortB] using h
      simp only [Compile.portTrace, List.mem_append, not_or] at hn
      rw [Compile.memPort,
        ihRight _ (by simpa [Compile.writesPortB] using hn.2),
        ihLeft _ (by simpa [Compile.writesPortB] using hn.1)]
  | ite guard thenAct elseAct ihThen ihElse =>
      intro cur h
      have hn : p ∉ Compile.portTrace mn
          (Loom.Hw.Act.ite guard thenAct elseAct) := by
        simpa [Compile.writesPortB] using h
      simp only [Compile.portTrace, List.mem_append, not_or] at hn
      rw [Compile.memPort, if_neg]
      simp [Compile.writesPortB, hn]
  | write => intro _ _; rfl
  | memWrite actualAw actualDw name port address value =>
      intro cur h
      have hn : p ∉ Compile.portTrace mn
          (Loom.Hw.Act.memWrite actualAw actualDw name port address value) := by
        simpa [Compile.writesPortB] using h
      simp only [Compile.memPort]
      by_cases hp : name = mn ∧ port = p
      · exact False.elim (hn (by simp [Compile.portTrace, hp]))
      · rw [if_neg hp]

/-- Check a supplied result of one memory-port action locally. -/
def nextPortMatches (mn : String) (aw dw p : Nat) : Loom.Hw.Act →
    Compile.Port aw dw → Compile.Port aw dw → NextPortCert aw dw → Bool
  | .skip, cur, out, .same => decide (out = cur)
  | .seq a b, cur, out, .seq mid ca cb =>
      nextPortMatches mn aw dw p a cur mid ca &&
        nextPortMatches mn aw dw p b mid out cb
  | .seq a b, cur, out, .same =>
      if Compile.writesPortB mn p (.seq a b) then false else decide (out = cur)
  | .ite c t e, cur, out, .ite g ot oe ct ce =>
      if Compile.writesPortB mn p t || Compile.writesPortB mn p e then
        compileExprMatches c g &&
          nextPortMatches mn aw dw p t cur ot ct &&
          nextPortMatches mn aw dw p e cur oe ce &&
          decide (out = {
            en := .mux g ot.en oe.en
            addr := .mux g ot.addr oe.addr
            data := .mux g ot.data oe.data })
      else false
  | .ite _ t e, cur, out, .same =>
      if Compile.writesPortB mn p t || Compile.writesPortB mn p e then false
      else decide (out = cur)
  | .memWrite aw' dw' mn' p' a v, cur, out, cert =>
      if _hp : mn' = mn ∧ p' = p then
        if hw : aw' = aw ∧ dw' = dw then
          match cert with
          | .write =>
              decide (out.en = .lit 1) &&
                compileExprMatches (hw.1 ▸ a) out.addr &&
                compileExprMatches (hw.2 ▸ v) out.data
          | _ => false
        else
          match cert with
          | .same => decide (out = cur)
          | _ => false
      else
        match cert with
        | .same => decide (out = cur)
        | _ => false
  | .write .., cur, out, .same => decide (out = cur)
  | _, _, _, _ => false

/-- A successful memory-port certificate recovers equality with the
reference `Compile.memPort` result. -/
theorem nextPortMatches_sound (mn : String) (aw dw p : Nat) :
    ∀ (a : Loom.Hw.Act) (cur out : Compile.Port aw dw)
      (cert : NextPortCert aw dw),
      nextPortMatches mn aw dw p a cur out cert = true →
        out = Compile.memPort mn aw dw p a cur := by
  intro a
  induction a <;> intro cur out cert h
  · cases cert <;> simp [nextPortMatches, Compile.memPort] at h ⊢
    exact h
  · rename_i a b iha ihb
    cases cert with
    | seq mid ca cb =>
        simp only [nextPortMatches, Bool.and_eq_true] at h
        rw [Compile.memPort]
        rw [ihb mid out cb h.2, iha cur mid ca h.1]
    | same =>
        simp only [nextPortMatches] at h
        split at h
        · contradiction
        · rename_i hn
          simp only [decide_eq_true_eq] at h
          rw [h, memPort_eq_of_no_write mn aw dw p (.seq a b) cur (by simpa using hn)]
    | _ => simp [nextPortMatches] at h
  · rename_i c t e iht ihe
    by_cases hwrites : Compile.writesPortB mn p t ||
        Compile.writesPortB mn p e
    · cases cert with
      | ite g ot oe ct ce =>
          simp only [nextPortMatches, hwrites, if_true, Bool.and_eq_true,
            decide_eq_true_eq] at h
          obtain ⟨⟨⟨hg, ht⟩, he⟩, hout⟩ := h
          rw [Compile.memPort, if_pos hwrites]
          simp only
          rw [hout, iht cur ot ct ht, ihe cur oe ce he,
            compileExprMatches_sound c g hg]
      | _ => simp [nextPortMatches, hwrites] at h
    · cases cert <;> simp [nextPortMatches, Compile.memPort, hwrites] at h ⊢
      exact h
  · cases cert <;> simp [nextPortMatches, Compile.memPort] at h ⊢
    exact h
  · rename_i aw' dw' mn' p' a v
    by_cases hp : mn' = mn ∧ p' = p
    · by_cases hw : aw' = aw ∧ dw' = dw
      · rcases hp with ⟨rfl, rfl⟩
        rcases hw with ⟨rfl, rfl⟩
        cases cert <;>
          simp [nextPortMatches, Compile.memPort] at h ⊢
        obtain ⟨⟨hen, ha⟩, hv⟩ := h
        cases out
        simp_all
        exact ⟨compileExprMatches_sound a _ ha,
          compileExprMatches_sound v _ hv⟩
      · cases cert <;>
          simp [nextPortMatches, Compile.memPort, hp, hw] at h ⊢
        exact h
    · cases cert <;> simp [nextPortMatches, Compile.memPort, hp] at h ⊢
      exact h

/-- Proof data for folding an ordered rule list into one write port. -/
inductive NextPortRulesCert (aw dw : Nat) where
  | nil
  | cons (mid : Compile.Port aw dw) (head : NextPortCert aw dw)
      (tail : NextPortRulesCert aw dw)

/-- Check a complete rule fold for one memory write port. -/
def nextPortRulesMatches (mn : String) (aw dw p : Nat) :
    List Loom.Hw.Rule → Compile.Port aw dw → Compile.Port aw dw →
      NextPortRulesCert aw dw → Bool
  | [], cur, out, .nil => decide (out = cur)
  | rl :: rls, cur, out, .cons mid ch ct =>
      nextPortMatches mn aw dw p rl.body cur mid ch &&
        nextPortRulesMatches mn aw dw p rls mid out ct
  | _, _, _, _ => false

/-- Successful write-port rule-fold validation recovers the reference fold. -/
theorem nextPortRulesMatches_sound (mn : String) (aw dw p : Nat) :
    ∀ (rules : List Loom.Hw.Rule) (cur out : Compile.Port aw dw)
      (cert : NextPortRulesCert aw dw),
      nextPortRulesMatches mn aw dw p rules cur out cert = true →
        out = rules.foldl
          (fun acc rl => Compile.memPort mn aw dw p rl.body acc) cur := by
  intro rules
  induction rules with
  | nil =>
      intro cur out cert h
      cases cert <;> simp [nextPortRulesMatches] at h ⊢
      exact h
  | cons rl rls ih =>
      intro cur out cert h
      cases cert with
      | cons mid ch ct =>
          simp only [nextPortRulesMatches, Bool.and_eq_true] at h
          simp only [List.foldl_cons]
          rw [ih mid out ct h.2,
            nextPortMatches_sound mn aw dw p rl.body cur mid ch h.1]
      | _ => simp [nextPortRulesMatches] at h

/-- Certificates for `n` consecutive compiled write ports. -/
inductive PortsCert (aw dw : Nat) : Nat → Type where
  | nil : PortsCert aw dw 0
  | cons {n} (head : NextPortRulesCert aw dw)
      (tail : PortsCert aw dw n) : PortsCert aw dw (n + 1)

set_option linter.unusedVariables false in
/-- Check consecutive write ports beginning at index `p`. -/
def portsMatch (mn : String) (aw dw : Nat) (rules : List Loom.Hw.Rule) :
    ∀ (p n : Nat), List (Compile.Port aw dw) → PortsCert aw dw n → Bool
  | _, 0, [], .nil => true
  | _, 0, _ :: _, .nil => false
  | p, n + 1, out :: outs, .cons ch ct =>
      nextPortRulesMatches mn aw dw p rules
        { en := .lit 0, addr := .lit 0, data := .lit 0 } out ch &&
      portsMatch mn aw dw rules (p + 1) n outs ct
  | _, _ + 1, [], .cons _ _ => false

/-- Successful consecutive-port validation recovers the reference compiler's
port list for the corresponding index interval. -/
theorem portsMatch_sound (mn : String) (aw dw : Nat)
    (rules : List Loom.Hw.Rule) :
    ∀ (p n : Nat) (outs : List (Compile.Port aw dw))
      (cert : PortsCert aw dw n),
      portsMatch mn aw dw rules p n outs cert = true →
        outs = (List.range' p n).map fun q =>
          rules.foldl (fun cur rl =>
            Compile.memPort mn aw dw q rl.body cur)
            { en := .lit 0, addr := .lit 0, data := .lit 0 }
  | _, 0, [], .nil, _ => rfl
  | _, 0, _ :: _, .nil, h => by simp [portsMatch] at h
  | _, _ + 1, [], .cons _ _, h => by simp [portsMatch] at h
  | p, n + 1, out :: outs, .cons ch ct, h => by
      simp only [portsMatch, Bool.and_eq_true] at h
      simp only [List.range'_succ, List.map_cons]
      rw [nextPortRulesMatches_sound mn aw dw p rules _ out ch h.1,
        portsMatch_sound mn aw dw rules (p + 1) n outs ct h.2]

/-! ## Output certificates -/

/-- Check the observability output generated for a source register. -/
def outMatches (r : Loom.Hw.RegDecl)
    (out : Loom.Emit.MicroVerilog.OutDef) : Bool :=
  decide (out.name = s!"o_{r.name}") &&
  if h : out.width = r.width then
    compileExprMatches (.reg r.width r.name) (h ▸ out.val)
  else false

/-- Successful output validation recovers the exact reference output. -/
theorem outMatches_sound (r : Loom.Hw.RegDecl)
    (out : Loom.Emit.MicroVerilog.OutDef)
    (h : outMatches r out = true) :
    out = ({ name := s!"o_{r.name}", width := r.width,
             val := .reg r.width r.name } : Loom.Emit.MicroVerilog.OutDef) := by
  unfold outMatches at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hrest⟩ := h
  split at hrest
  · rename_i hw
    have hv := compileExprMatches_sound (.reg r.width r.name)
      (hw ▸ out.val) hrest
    cases r
    cases out
    simp at hn hw hv ⊢
    cases hn
    cases hw
    cases hv
    simp
  · contradiction

/-- Check the complete output list against the source register list. -/
def outsMatch : List Loom.Hw.RegDecl →
    List Loom.Emit.MicroVerilog.OutDef → Bool
  | [], [] => true
  | r :: rs, out :: outs => outMatches r out && outsMatch rs outs
  | _, _ => false

/-- Successful output-list validation recovers the reference output list. -/
theorem outsMatch_sound : ∀ (rs : List Loom.Hw.RegDecl)
    (outs : List Loom.Emit.MicroVerilog.OutDef),
    outsMatch rs outs = true →
      outs = rs.map fun r =>
        ({ name := s!"o_{r.name}", width := r.width,
           val := .reg r.width r.name } : Loom.Emit.MicroVerilog.OutDef)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [outsMatch] at h
  | _ :: _, [], h => by simp [outsMatch] at h
  | r :: rs, out :: outs, h => by
      simp only [outsMatch, Bool.and_eq_true, List.map_cons] at h ⊢
      rw [outMatches_sound r out h.1, outsMatch_sound rs outs h.2]

/-! ## Memory-definition certificates -/

/-- The reference memory definition contributed by one source declaration. -/
def compiledMem (d : Loom.Hw.Design) (m : Loom.Hw.MemDecl) :
    Loom.Emit.MicroVerilog.MemDef where
  name := m.name
  addrWidth := m.addrWidth
  dataWidth := m.dataWidth
  init := m.init
  wrPorts := (List.range (Compile.numPorts d m.name)).map fun p =>
    Compile.compilePort d m.name m.addrWidth m.dataWidth p

/-- Certificate for all write ports of one source memory. -/
structure MemCert (d : Loom.Hw.Design) (m : Loom.Hw.MemDecl) where
  ports : PortsCert m.addrWidth m.dataWidth (Compile.numPorts d m.name)

/-- Check memory metadata, its complete addressable initialization image,
and every generated write port. -/
def memMatches (d : Loom.Hw.Design) (m : Loom.Hw.MemDecl)
    (out : Loom.Emit.MicroVerilog.MemDef) (cert : MemCert d m) : Bool :=
  decide (out.name = m.name) &&
  if haw : out.addrWidth = m.addrWidth then
    if hdw : out.dataWidth = m.dataWidth then
      decide (∀ i, i < 2 ^ m.addrWidth →
        ((hdw ▸ out.init) i).toNat = (m.init i).toNat) &&
      portsMatch m.name m.addrWidth m.dataWidth d.rules 0
        (Compile.numPorts d m.name) (haw ▸ (hdw ▸ out.wrPorts)) cert.ports
    else false
  else false

private theorem init_cast_sound {outAw srcAw outDw srcDw : Nat}
    (haw : outAw = srcAw) (hdw : outDw = srcDw)
    (outInit : Nat → BitVec outDw) (srcInit : Nat → BitVec srcDw)
    (h : ∀ i, i < 2 ^ srcAw →
      ((hdw ▸ outInit) i).toNat = (srcInit i).toNat) :
    ∀ i, i < 2 ^ outAw →
      (outInit i).toNat = (srcInit i).toNat := by
  cases haw
  cases hdw
  exact h

/-- Successful memory validation proves agreement with the reference
compiler on every field observable in emitted Verilog. -/
theorem memMatches_sound (d : Loom.Hw.Design) (m : Loom.Hw.MemDecl)
    (out : Loom.Emit.MicroVerilog.MemDef) (cert : MemCert d m)
    (h : memMatches d m out cert = true) :
    out.Matches (compiledMem d m) := by
  unfold memMatches at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, hrest⟩ := h
  split at hrest
  · rename_i haw
    split at hrest
    · rename_i hdw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
      obtain ⟨hi, hpcheck⟩ := hrest
      have hp := portsMatch_sound m.name m.addrWidth m.dataWidth d.rules 0
        (Compile.numPorts d m.name) (haw ▸ (hdw ▸ out.wrPorts))
        cert.ports hpcheck
      simp only [List.range'_eq_map_range, Nat.zero_add, List.map_map] at hp
      have hcast : HEq out.wrPorts (haw ▸ (hdw ▸ out.wrPorts)) :=
        HEq.trans
          (eqRec_heq (φ := fun w =>
            List (Loom.Emit.MicroVerilog.WritePort out.addrWidth w))
            hdw out.wrPorts).symm
          (eqRec_heq (φ := fun w =>
            List (Loom.Emit.MicroVerilog.WritePort w m.dataWidth))
            haw (hdw ▸ out.wrPorts)).symm
      have hports : HEq out.wrPorts (compiledMem d m).wrPorts :=
        HEq.trans hcast (heq_of_eq hp)
      refine ⟨hn, haw, hdw, hports, ?_⟩
      exact init_cast_sound haw hdw out.init m.init hi
    · contradiction
  · contradiction

/-- A dependent certificate list aligned with source memory declarations. -/
inductive MemsCert (d : Loom.Hw.Design) : List Loom.Hw.MemDecl → Type where
  | nil : MemsCert d []
  | cons {m ms} (head : MemCert d m) (tail : MemsCert d ms) :
      MemsCert d (m :: ms)

/-- Check the complete supplied memory list in declaration order. -/
def memsMatch (d : Loom.Hw.Design) : ∀ {ms : List Loom.Hw.MemDecl},
    List Loom.Emit.MicroVerilog.MemDef → MemsCert d ms → Bool
  | [], [], .nil => true
  | [], _ :: _, .nil => false
  | _ :: _, [], .cons _ _ => false
  | m :: _, out :: outs, .cons ch ct =>
      memMatches d m out ch && memsMatch d outs ct

/-- Successful memory-list validation gives pairwise `MemDef.Matches`
against the reference compiler's list. -/
theorem memsMatch_sound (d : Loom.Hw.Design) :
    ∀ {ms : List Loom.Hw.MemDecl}
      (outs : List Loom.Emit.MicroVerilog.MemDef) (cert : MemsCert d ms),
      memsMatch d outs cert = true →
        List.Forall₂ Loom.Emit.MicroVerilog.MemDef.Matches outs
          (ms.map (compiledMem d))
  | [], [], .nil, _ => .nil
  | [], _ :: _, .nil, h => by simp [memsMatch] at h
  | _ :: _, [], .cons _ _, h => by simp [memsMatch] at h
  | m :: ms, out :: outs, .cons ch ct, h => by
      simp only [memsMatch, Bool.and_eq_true] at h
      exact .cons (memMatches_sound d m out ch h.1)
        (memsMatch_sound d outs ct h.2)

/-! ## Whole-module certificates -/

/-- Certificate data for every dependent component of a compiled design. -/
structure ModuleCert (d : Loom.Hw.Design) where
  regs : RegsCert d.regs
  mems : MemsCert d d.mems

/-- Check a supplied µVerilog module against the reference compiler locally. -/
def moduleMatches (d : Loom.Hw.Design)
    (out : Loom.Emit.MicroVerilog.Module) (cert : ModuleCert d) : Bool :=
  decide (out.name = d.name) &&
  regsMatch d.rules out.regs cert.regs &&
  memsMatch d out.mems cert.mems &&
  outsMatch d.regs out.outs

/-- The whole-module checker is sound: acceptance proves the supplied module
matches `Compile.compile d` on every Verilog-observable field. -/
theorem moduleMatches_sound (d : Loom.Hw.Design)
    (out : Loom.Emit.MicroVerilog.Module) (cert : ModuleCert d)
    (h : moduleMatches d out cert = true) :
    out.Matches (Compile.compile d) := by
  simp only [moduleMatches, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hrcheck⟩, hmcheck⟩, hocheck⟩ := h
  have hr := regsMatch_sound d.rules out.regs cert.regs hrcheck
  have hm := memsMatch_sound d out.mems cert.mems hmcheck
  have ho := outsMatch_sound d.regs out.outs hocheck
  refine ⟨hn, ?_, ?_, ?_⟩
  · simpa only [Compile.compile] using hr
  · simpa only [Compile.compile] using ho
  · simpa only [Compile.compile, compiledMem, Compile.compilePort] using hm

/-! ## Exact-text release certificates -/

/-- Check the exact supplied Verilog text by parsing it, then validate the
resulting module against the reference compiler using proof data. -/
def artifactMatches (d : Loom.Hw.Design) (text : String)
    (cert : ModuleCert d) : Bool :=
  match Loom.Emit.MicroVerilog.Parse.parse text with
  | some out => moduleMatches d out cert
  | none => false

/-- An accepted exact-text certificate closes the release boundary: the
literal supplied text parses to a module matching the proved compiler. -/
theorem artifactMatches_sound (d : Loom.Hw.Design) (text : String)
    (cert : ModuleCert d) (h : artifactMatches d text cert = true) :
    ∃ out, Loom.Emit.MicroVerilog.Parse.parse text = some out ∧
      out.Matches (Compile.compile d) := by
  unfold artifactMatches at h
  split at h
  · rename_i out hparse
    exact ⟨out, hparse, moduleMatches_sound d out cert h⟩
  · contradiction

end Loom.Hw.ArtifactCert
