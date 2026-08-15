-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.Print

/-!
# Finite-trace properties and an SVA bridge

`Property.holdsAt` is the primary semantics. The SVA renderer covers the same
small, explicit fragment and emits history-valid gating so first-sample
behavior never depends on four-state `$past` initialization. External formal
tools remain evidence producers; they do not replace these Loom semantics.
-/

namespace Loom.Hw

namespace Temporal

/-- An existentially width-indexed observed expression. -/
structure Signal where
  width : Nat
  value : Expr width

namespace Signal

def ofExpr {width : Nat} (value : Expr width) : Signal := ⟨width, value⟩

def equalAt (signal : Signal) (left right : St) : Bool :=
  signal.value.eval left == signal.value.eval right

end Signal

/-- The conventional property subset whose sampling semantics Loom fixes. -/
inductive Property where
  | atom (condition : Expr 1)
  | not (property : Property)
  | and (left right : Property)
  | or (left right : Property)
  | implies (premise conclusion : Property)
  | next (property : Property)
  | always (property : Property)
  | eventuallyWithin (ticks : Nat) (property : Property)
  | past (condition : Expr 1) (initial : Bool)
  | rose (condition : Expr 1)
  | fell (condition : Expr 1)
  | stable (signal : Signal)

namespace Property

private def asserted (condition : Expr 1) (state : St) : Bool :=
  condition.eval state == 1#1

/-- Finite-trace semantics at one sample. `next` is false at the final sample;
bounded eventuality searches the inclusive `[now, now + ticks]` window.
History operators have explicit sample-zero behavior. -/
def holdsAt (states : List St) (index : Nat) : Property → Bool
  | .atom condition =>
      match states[index]? with
      | some state => asserted condition state
      | none => false
  | .not property => !(holdsAt states index property)
  | .and left right => holdsAt states index left && holdsAt states index right
  | .or left right => holdsAt states index left || holdsAt states index right
  | .implies premise conclusion =>
      !(holdsAt states index premise) || holdsAt states index conclusion
  | .next property => holdsAt states (index + 1) property
  | .always property =>
      (List.range (states.length - index)).all fun offset =>
        holdsAt states (index + offset) property
  | .eventuallyWithin ticks property =>
      (List.range (ticks + 1)).any fun offset =>
        holdsAt states (index + offset) property
  | .past condition initial =>
      if index == 0 then initial
      else match states[index - 1]? with
        | some state => asserted condition state
        | none => false
  | .rose condition =>
      if index == 0 then false
      else match states[index - 1]?, states[index]? with
        | some before, some now => !asserted condition before && asserted condition now
        | _, _ => false
  | .fell condition =>
      if index == 0 then false
      else match states[index - 1]?, states[index]? with
        | some before, some now => asserted condition before && !asserted condition now
        | _, _ => false
  | .stable signal =>
      if index == 0 then true
      else match states[index - 1]?, states[index]? with
        | some before, some now => signal.equalAt before now
        | _, _ => false
termination_by property => property

def holds (states : List St) (property : Property) : Bool :=
  holdsAt states 0 property

private abbrev RenderM := StateM Loom.Emit.MicroVerilog.Print.PSt

private def renderExpr {width : Nat} (expression : Expr width) : RenderM String :=
  Loom.Emit.MicroVerilog.Print.pExpr (Compile.compileExpr expression)

private def render : Property → RenderM String
  | .atom condition => renderExpr condition
  | .not property => return s!"!({← render property})"
  | .and left right => return s!"({← render left}) && ({← render right})"
  | .or left right => return s!"({← render left}) || ({← render right})"
  | .implies premise conclusion =>
      return s!"({← render premise}) |-> ({← render conclusion})"
  | .next property => return s!"nexttime ({← render property})"
  | .always property => return s!"always ({← render property})"
  | .eventuallyWithin ticks property =>
      return s!"1'b1 |-> ##[0:{ticks}] ({← render property})"
  | .past condition initial => do
      let value ← renderExpr condition
      let initialBit := if initial then "1'b1" else "1'b0"
      return s!"(!loom_history_valid ? {initialBit} : $past({value}))"
  | .rose condition =>
      return s!"(loom_history_valid && $rose({← renderExpr condition}))"
  | .fell condition =>
      return s!"(loom_history_valid && $fell({← renderExpr condition}))"
  | .stable signal =>
      return s!"(!loom_history_valid || $stable({← renderExpr signal.value}))"

inductive Directive where
  | assert
  | assume
  | cover
  deriving Repr, DecidableEq, BEq

structure Named where
  name : String
  property : Property
  directive : Directive := .assert

/-- Render one property for insertion into the design module. The generated
SSA wires use the same µVerilog expression printer as RTL emission. -/
def toSva (named : Named) : Except String String := do
  if named.name.isEmpty then throw "temporal property name must not be empty"
  let (body, printer) := (render named.property).run {}
  let wires := String.intercalate "\n" printer.lines.toList
  let directive := match named.directive with
    | .assert => "assert"
    | .assume => "assume"
    | .cover => "cover"
  return String.intercalate "\n"
    [wires,
     "  logic loom_history_valid;",
     "  always_ff @(posedge clk) begin",
     "    if (rst) loom_history_valid <= 1'b0;",
     "    else loom_history_valid <= 1'b1;",
     "  end",
     s!"  {named.name}: {directive} property (@(posedge clk) disable iff (rst) ({body}));"]

end Property

inductive FormalMode where
  | prove
  | cover
  deriving Repr, DecidableEq, BEq

inductive FormalEngine where
  | smtbmc
  | abcPdr
  deriving Repr, DecidableEq, BEq

/-- A bounded external-formal invocation plan. Positive depth is established
once, at construction, rather than revalidated by every backend. -/
structure SymbiYosysPlan where
  top : String
  rtlFile : String
  propertyFile : String
  mode : FormalMode
  engine : FormalEngine := .smtbmc
  depth : Nat
  depthPositive : 0 < depth

namespace SymbiYosysPlan

def checked (top rtlFile propertyFile : String) (mode : FormalMode)
    (depth : Nat) (engine : FormalEngine := .smtbmc) :
    Except String SymbiYosysPlan := do
  if top.isEmpty || rtlFile.isEmpty || propertyFile.isEmpty then
    throw "SymbiYosys plan requires nonempty top, RTL, and property file names"
  if positive : 0 < depth then
    return ⟨top, rtlFile, propertyFile, mode, engine, depth, positive⟩
  else throw "SymbiYosys bounded depth must be positive"

private def modeName : FormalMode → String
  | .prove => "prove"
  | .cover => "cover"

private def engineName : FormalEngine → String
  | .smtbmc => "smtbmc"
  | .abcPdr => "abc pdr"

/-- Deterministic `.sby` text. Running the named tool and interpreting its
result remain external evidence steps. -/
def render (plan : SymbiYosysPlan) : String :=
  String.intercalate "\n"
    ["[options]", "mode " ++ modeName plan.mode, s!"depth {plan.depth}",
     "", "[engines]", engineName plan.engine,
     "", "[script]", s!"read -formal {plan.rtlFile} {plan.propertyFile}",
     s!"prep -top {plan.top}",
     "", "[files]", plan.rtlFile, plan.propertyFile, ""]

end SymbiYosysPlan

/-- Reports never conflate a checked Loom result with an external engine's
claim. -/
inductive EvidenceStatus where
  | loomChecked
  | externalPass
  | externalFail
  | unsupported
  deriving Repr, DecidableEq, BEq

end Temporal

end Loom.Hw
