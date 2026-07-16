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

/-- Check a supplied result of one `nextReg` action locally. -/
def nextRegMatches (rn : String) (w : Nat) : Loom.Hw.Act →
    Loom.Emit.MicroVerilog.Expr w → Loom.Emit.MicroVerilog.Expr w →
    NextRegCert w → Bool
  | .skip, cur, out, .same => decide (out = cur)
  | .seq a b, cur, out, .seq mid ca cb =>
      nextRegMatches rn w a cur mid ca &&
        nextRegMatches rn w b mid out cb
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

/-- Check a supplied result of one memory-port action locally. -/
def nextPortMatches (mn : String) (aw dw p : Nat) : Loom.Hw.Act →
    Compile.Port aw dw → Compile.Port aw dw → NextPortCert aw dw → Bool
  | .skip, cur, out, .same => decide (out = cur)
  | .seq a b, cur, out, .seq mid ca cb =>
      nextPortMatches mn aw dw p a cur mid ca &&
        nextPortMatches mn aw dw p b mid out cb
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

end Loom.Hw.ArtifactCert
