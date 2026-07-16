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

end Loom.Hw.ArtifactCert
