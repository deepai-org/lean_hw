-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Notation

/-!
# Single-source design declarations

`Declarations` is a small, immutable authoring layer for a `Design` interface.
Typed handles contribute their core declaration and adjacent interface policy
in one call; `Design.ofDecls` then lowers the result to the existing `Design`
fields.  It adds no new semantics or validation boundary: the ordinary design
checks still reject duplicate names, invalid outputs, and inconsistent policy.

Nothing here changes hand-written `Design` values.  In particular, exports
remain opt-in and memory policy defaults remain conservative.
-/

namespace Loom.Hw

/-- One value for one typed input handle. The dependent width keeps the port
and value aligned while allowing heterogeneous bindings in one list. -/
structure InputBinding where
  width : Nat
  port : Reg width
  value : BitVec width

namespace InputBinding

/-- Package a typed port and value without restating either name or width. -/
def of {w : Nat} (port : Reg w) (value : BitVec w) : InputBinding :=
  ⟨w, port, value⟩

/-- Lower typed bindings to Loom's open-design environment function. Both the
name and declared width must match; an inconsistent query fails closed. -/
def toEnv (bindings : List InputBinding) : InEnv := fun name width =>
  match bindings.find? (fun binding =>
      binding.port.name = name && binding.width = width) with
  | some binding => binding.value.setWidth width
  | none => 0#width

end InputBinding

/-- Declarations and interface policy accumulated before rules are attached. -/
structure Declarations where
  regs : List RegDecl := []
  mems : List MemDecl := []
  inputs : List InputDecl := []
  outputs : List String := []
  combOutputs : List CombOutput := []
  ackMemInit : List String := []
  syncReadMems : List String := []

namespace Declarations

/-- An empty declaration set. -/
@[simp] def empty : Declarations := {}

/-- Add one register and, when requested, export it at the design boundary. -/
@[simp] def addReg {w : Nat} (ds : Declarations) (r : Reg w)
    (init : BitVec w := 0) (exported : Bool := false) : Declarations :=
  { ds with
    regs := ds.regs ++ [r.decl init]
    outputs := if exported then ds.outputs ++ [r.name] else ds.outputs }

/-- Add a complete register family in index order. -/
@[simp] def addRegArray {w n : Nat} (ds : Declarations) (ra : RegArray w n)
    (init : Fin n → BitVec w := fun _ => 0)
    (exported : Bool := false) : Declarations :=
  let regs := ra.decls init
  { ds with
    regs := ds.regs ++ regs
    outputs := if exported then ds.outputs ++ regs.map (·.name) else ds.outputs }

/-- Add an environment-owned input. -/
@[simp] def addInput {w : Nat} (ds : Declarations) (input : Reg w) : Declarations :=
  { ds with inputs := ds.inputs ++ [input.input] }

/-- Add a same-cycle output expression. Its width is carried by the
expression, so an output cannot be declared at a width different from the
value that drives it. -/
@[simp] def addCombOutput {w : Nat} (ds : Declarations) (name : String)
    (value : Expr w) : Declarations :=
  { ds with combOutputs := ds.combOutputs ++ [⟨name, w, value⟩] }

/-- Add a memory together with its initialization and implementation policy. -/
@[simp] def addMem {aw dw : Nat} (ds : Declarations) (mem : Mem aw dw)
    (init : Nat → BitVec dw := fun _ => 0)
    (syncRead : Bool := false) (ackInit : Bool := false) : Declarations :=
  { ds with
    mems := ds.mems ++ [mem.decl init]
    syncReadMems :=
      if syncRead then ds.syncReadMems ++ [mem.name] else ds.syncReadMems
    ackMemInit := if ackInit then ds.ackMemInit ++ [mem.name] else ds.ackMemInit }

end Declarations

/-- Attach rules to a declaration set, producing the unchanged core `Design`. -/
@[simp] def Design.ofDecls (name : String) (decls : Declarations)
    (rules : List Rule) : Design where
  name := name
  regs := decls.regs
  mems := decls.mems
  rules := rules
  inputs := decls.inputs
  ackMemInit := decls.ackMemInit
  syncReadMems := decls.syncReadMems
  outputs := decls.outputs
  combOutputs := decls.combOutputs

end Loom.Hw
