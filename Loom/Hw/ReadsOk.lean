-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Syntax

/-!
# W1.1 — the read side of declaration checking

`Compile.designWFCheck` constrains **writes**: a rule may not write a signal
the design does not declare. Reads had no such gate, and the failure mode is
worse than a write typo because it is **silent**: `Expr.reg w "cnt"` against a
design that declares `cnt` at a different width, or spells it `count`,
evaluates to `0#w` forever. Nothing errors, nothing warns, and the design
simulates and emits — it is just wrong.

This is the same shape as D19/D38/D39: a property the design must have, made
an emit-time refusal so a caller cannot skip it. `Design.emit` runs it.

**What counts as declared.** A `.reg w n` read resolves against the declared
registers *and* the D15 input ports (inputs are read with `Expr.reg` by
design — they are environment-owned coordinates). A `.memRead dw m a`
resolves against the declared memories, checking the data width and
recursing into the address expression.
-/

namespace Loom.Hw

/-- Every `(name, width)` a register-read occurs at, plus every
`(mem, dataWidth)` a memory-read occurs at, in one pass. -/
def Expr.readSites : {w : Nat} → Expr w → List (String × Nat) × List (String × Nat)
  | _, .lit _         => ([], [])
  | w, .reg _ n       => ([(n, w)], [])
  | _, .memRead dw m a =>
      let (r, s) := a.readSites; (r, (m, dw) :: s)
  | _, .and a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .or a b        => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .xor a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .not a         => a.readSites
  | _, .add a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .sub a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .mul a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .shl a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .shr a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .eq a b        => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .ult a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .slt a b       => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | _, .mux c t f     =>
      let (r,s) := c.readSites; let (r',s') := t.readSites; let (r'',s'') := f.readSites
      (r++r'++r'', s++s'++s'')
  | _, .slice a _ _   => a.readSites
  | _, .zext a _      => a.readSites
  | _, .sext a _      => a.readSites

/-- The read sites of an action, including the guards of `ite` and the
address/data of `memWrite`. -/
def Act.readSites : Act → List (String × Nat) × List (String × Nat)
  | .skip => ([], [])
  | .seq a b => let (r,s) := a.readSites; let (r',s') := b.readSites; (r++r', s++s')
  | .ite c t e =>
      let (r,s) := c.readSites; let (r',s') := t.readSites; let (r'',s'') := e.readSites
      (r++r'++r'', s++s'++s'')
  | .write _ _ v => v.readSites
  | .memWrite _ _ _ _ a v =>
      let (r,s) := a.readSites; let (r',s') := v.readSites; (r++r', s++s')

/-- Every read site in the design. -/
def Design.readSites (d : Design) : List (String × Nat) × List (String × Nat) :=
  d.rules.foldl (fun (acc : List (String × Nat) × List (String × Nat)) rule =>
    let (r, s) := rule.body.readSites; (acc.1 ++ r, acc.2 ++ s)) ([], [])

/-- Register reads that name nothing declared, or name it at the wrong width.
Inputs count as declared: D15 inputs are read with `Expr.reg`. -/
def Design.badRegReads (d : Design) : List (String × Nat) :=
  d.readSites.1.filter fun (n, w) =>
    !((d.regs.any fun r => r.name = n && r.width = w) ||
      (d.inputs.any fun i => i.name = n && i.width = w))

/-- Memory reads that name no declared memory, or the wrong data width. -/
def Design.badMemReads (d : Design) : List (String × Nat) :=
  d.readSites.2.filter fun (m, dw) =>
    !(d.mems.any fun md => md.name = m && md.dataWidth = dw)

/-- **The W1.1 check.** Every read resolves to a declaration at that width. -/
def Design.readsOkB (d : Design) : Bool :=
  d.badRegReads.isEmpty && d.badMemReads.isEmpty

/-- Refusal message for a bad register read. Names the closest declaration
so a width mismatch reads differently from a typo. -/
def Design.badRegReadError (d : Design) (n : String) (w : Nat) : String :=
  match d.regs.find? (·.name = n), d.inputs.find? (·.name = n) with
  | some r, _ =>
      s!"Design.emit: design '{d.name}' reads register '{n}' at width {w}, \
but it is declared at width {r.width}. A wrong-width read is SILENT without \
this check — it evaluates to 0 forever (W1.1)."
  | _, some i =>
      s!"Design.emit: design '{d.name}' reads input '{n}' at width {w}, but \
it is declared at width {i.width} (W1.1)."
  | none, none =>
      s!"Design.emit: design '{d.name}' reads '{n}' (width {w}), which is \
neither a declared register nor a declared input. A read of an undeclared \
name is SILENT without this check — it evaluates to 0 forever, so a typo \
becomes a design that simulates and emits and is simply wrong (W1.1)."

/-- Refusal message for a bad memory read. -/
def Design.badMemReadError (d : Design) (m : String) (dw : Nat) : String :=
  match d.mems.find? (·.name = m) with
  | some md =>
      s!"Design.emit: design '{d.name}' reads memory '{m}' at data width \
{dw}, but it is declared at {md.dataWidth} (W1.1)."
  | none =>
      s!"Design.emit: design '{d.name}' reads memory '{m}', which is not \
declared (W1.1)."

end Loom.Hw
