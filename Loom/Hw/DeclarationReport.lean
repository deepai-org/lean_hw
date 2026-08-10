-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations

/-!
# Declaration migration reports

An incremental typed-handle migration needs a refusal boundary before it
rewrites behavior.  This module compares the complete structural interface of
two declaration sets in order: register names, widths and reset values;
memory names and dimensions; inputs; outputs; and memory-policy lists.

Memory initialization functions are intentionally not compared here because
function equality is not decidable.  A migration with non-zero memory images
must retain a separate definitional or extensional image theorem.  The report
says this explicitly instead of silently sampling an image.
-/

namespace Loom.Hw

/-- The decidable part of one design declaration or interface-policy entry. -/
inductive DeclarationShape where
  | reg (width init : Nat)
  | mem (addrWidth dataWidth : Nat)
  | input (width : Nat)
  | output
  | ackMemInit
  | syncReadMem
  deriving Repr, BEq, DecidableEq

/-- A named declaration shape. List position remains significant. -/
structure DeclarationEntry where
  name : String
  shape : DeclarationShape
  deriving Repr, BEq, DecidableEq

private def entriesOf (regs : List RegDecl) (mems : List MemDecl)
    (inputs : List InputDecl) (outputs ackMemInit syncReadMems : List String) :
    List DeclarationEntry :=
  regs.map (fun r => ⟨r.name, .reg r.width r.init.toNat⟩) ++
  mems.map (fun m => ⟨m.name, .mem m.addrWidth m.dataWidth⟩) ++
  inputs.map (fun i => ⟨i.name, .input i.width⟩) ++
  outputs.map (fun name => ⟨name, .output⟩) ++
  ackMemInit.map (fun name => ⟨name, .ackMemInit⟩) ++
  syncReadMems.map (fun name => ⟨name, .syncReadMem⟩)

/-- The complete decidable declaration surface of a builder value. -/
def Declarations.entries (d : Declarations) : List DeclarationEntry :=
  entriesOf d.regs d.mems d.inputs d.outputs d.ackMemInit d.syncReadMems

/-- The complete decidable declaration surface of a lowered design. -/
def Design.declarationEntries (d : Design) : List DeclarationEntry :=
  entriesOf d.regs d.mems d.inputs d.outputs d.ackMemInit d.syncReadMems

private def entryText (entry : DeclarationEntry) : String :=
  s!"{entry.name}: {reprStr entry.shape}"

/-- Ordered, declaration-by-declaration differences. An empty result means
the complete decidable interface agrees, including order and policy. -/
def declarationDiff : List DeclarationEntry → List DeclarationEntry → List String
  | [], [] => []
  | expected :: expecteds, actual :: actuals =>
      let tail := declarationDiff expecteds actuals
      if expected == actual then tail
      else s!"expected {entryText expected}; actual {entryText actual}" :: tail
  | expected :: expecteds, [] =>
      s!"missing {entryText expected}" :: declarationDiff expecteds []
  | [], actual :: actuals =>
      s!"unexpected {entryText actual}" :: declarationDiff [] actuals

/-- Boolean gate for declaration migrations. -/
def declarationMigrationOkB (expected actual : List DeclarationEntry) : Bool :=
  (declarationDiff expected actual).isEmpty

/-- Human-readable report. Success still names the number of checked entries
and the deliberate memory-image exclusion. -/
def declarationMigrationReport (expected actual : List DeclarationEntry) : String :=
  let differences := declarationDiff expected actual
  let imageNote :=
    "memory init functions: not compared (retain a separate image theorem for non-zero images)"
  if differences.isEmpty then
    s!"OK: {expected.length} declaration entries agree\n{imageNote}"
  else
    s!"FAIL: {differences.length} declaration differences\n" ++
      String.intercalate "\n" differences ++ "\n" ++ imageNote

@[simp] theorem Design.ofDecls_declarationEntries (name : String)
    (decls : Declarations) (rules : List Rule) :
    (Design.ofDecls name decls rules).declarationEntries = decls.entries := rfl

end Loom.Hw
