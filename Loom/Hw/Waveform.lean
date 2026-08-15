-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Artifact

/-!
# Replayable waveform traces

The proved Loom semantics remains the simulator. This module records its
declared inputs, registers, and combinational outputs in a portable trace and
renders that trace as VCD. A trace carries the exact bytes of the artifact it
describes; VCD is an observation format, not a second execution engine.
-/

namespace Loom.Hw

namespace Waveform

/-- A dependently sized signal value. -/
structure Value where
  name : String
  width : Nat
  bits : BitVec width
  deriving Repr, DecidableEq, BEq

/-- One dependently sized environment drive. -/
structure Drive where
  name : String
  width : Nat
  value : BitVec width
  deriving Repr, DecidableEq, BEq

namespace Drive

def ofInput (input : InputDecl) (value : BitVec input.width) : Drive :=
  ⟨input.name, input.width, value⟩

end Drive

private def driveMatches (drive : Drive) (input : InputDecl) : Bool :=
  drive.name == input.name && drive.width == input.width

/-- Exact input vectors have one correctly-sized drive for every declared
input and no extras. -/
def inputsValidB (design : Design) (drives : List Drive) : Bool :=
  drives.length == design.inputs.length &&
    design.inputs.all (fun input =>
      (drives.filter fun drive => driveMatches drive input).length == 1) &&
    drives.all (fun drive => design.inputs.any (driveMatches drive))

private def inputEnv (drives : List Drive) : InEnv := fun name width =>
  match drives.find? fun drive => drive.name == name && drive.width == width with
  | none => 0#width
  | some drive =>
      if equal : drive.width = width then equal ▸ drive.value else 0#width

structure Stimulus where
  reset : Bool
  drives : List Drive
  deriving Repr, DecidableEq, BEq

/-- Only a stimulus proven complete for this exact design can reach the trace
runner. Use `checked` at dynamic boundaries. -/
structure ValidatedStimulus (design : Design) where
  stimulus : Stimulus
  valid : inputsValidB design stimulus.drives = true

namespace ValidatedStimulus

def checked (design : Design) (stimulus : Stimulus) :
    Except String (ValidatedStimulus design) :=
  if valid : inputsValidB design stimulus.drives = true then .ok ⟨stimulus, valid⟩
  else .error s!"waveform stimulus does not drive exactly the declared inputs of design '{design.name}'"

end ValidatedStimulus

/-- Stable observation schema. Registers include internal state because a
waveform is a debugging artifact; this does not alter module-port exposure. -/
def observe (design : Design) (inputs : InEnv) (state : St) : List Value :=
  design.inputs.map (fun input =>
      ⟨"input." ++ input.name, input.width, inputs input.name input.width⟩) ++
    design.regs.map (fun register =>
      ⟨"state." ++ register.name, register.width,
        state.regs register.name register.width⟩) ++
    design.combOutputs.map (fun output =>
      ⟨"output." ++ output.name, output.width,
        design.evalCombOutput inputs state output⟩)

structure Cycle where
  index : Nat
  stimulus : Stimulus
  before : List Value
  after : List Value
  deriving Repr, DecidableEq, BEq

/-- Serializable/replayable trace envelope. `artifact` retains exact bytes,
so associating evidence with another emitted design requires byte equality. -/
structure Trace where
  designName : String
  artifact : Loom.Artifact.Identity
  cycles : List Cycle
  deriving BEq

private def recordFrom (design : Design) :
    Nat → St → List (ValidatedStimulus design) → List Cycle
  | _, _, [] => []
  | index, state, stimulus :: rest =>
      let inputs := inputEnv stimulus.stimulus.drives
      let next := design.cycleOpenWithReset stimulus.stimulus.reset inputs state
      { index
        stimulus := stimulus.stimulus
        before := observe design inputs state
        after := observe design inputs next } ::
        recordFrom design (index + 1) next rest

def record (design : Design) (artifact : Loom.Artifact.Identity)
    (stimuli : List (ValidatedStimulus design)) : Trace :=
  ⟨design.name, artifact, recordFrom design 0 design.reset stimuli⟩

/-- Replay against the primary semantics and compare every declared observed
value. This intentionally checks the artifact identity as exact bytes. -/
def replayB (design : Design) (artifact : Loom.Artifact.Identity)
    (stimuli : List (ValidatedStimulus design)) (trace : Trace) : Bool :=
  trace.designName == design.name && trace.artifact == artifact &&
    trace.cycles == (record design artifact stimuli).cycles

private def binaryDigits (width : Nat) (value : Nat) : String :=
  let raw := String.ofList (Nat.toDigits 2 value)
  String.ofList (List.replicate (width - raw.length) '0') ++ raw

private def renderValue (id : String) (value : Value) : String :=
  if value.width == 1 then
    (if value.bits.toNat == 0 then "0" else "1") ++ id
  else
    "b" ++ binaryDigits value.width value.bits.toNat ++ " " ++ id

private def signalIds (values : List Value) : List (Value × String) :=
  values.zipIdx.map fun pair => (pair.1, "v" ++ toString pair.2)

private def renderValues (ids : List (Value × String))
    (values : List Value) : String :=
  String.intercalate "\n" <| ids.filterMap fun entry =>
    values.find? (fun value => value.name == entry.1.name) |>.map
      (renderValue entry.2)

/-- Deterministic VCD rendering. Each Loom cycle is one low phase followed by
the rising edge and post-edge observations. -/
def renderVcd (trace : Trace) : Except String String := do
  let some first := trace.cycles.head?
    | throw "cannot render an empty waveform trace"
  let ids := signalIds first.before
  let declarations := String.intercalate "\n" <|
    ["$var wire 1 clk clk $end", "$var wire 1 rst rst $end"] ++
      ids.map fun entry =>
        s!"$var wire {entry.1.width} {entry.2} {entry.1.name} $end"
  let body := String.intercalate "\n" <| trace.cycles.flatMap fun cycle =>
    [s!"#{2 * cycle.index}", "0clk",
      (if cycle.stimulus.reset then "1rst" else "0rst"),
      renderValues ids cycle.before,
      s!"#{2 * cycle.index + 1}", "1clk", renderValues ids cycle.after]
  return String.intercalate "\n"
    ["$timescale 1ns $end", "$scope module " ++ trace.designName ++ " $end",
     declarations, "$upscope $end", "$enddefinitions $end", body, ""]

end Waveform

end Loom.Hw
