-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CertifiedDesign
import Loom.Hw.System
import Loom.Hw.Diff
import Loom.Hw.ChanRefinement

/-!
# Certified multi-clock System simulator

`CertifiedSystem` packages one `CertifiedDesign` for every named island.
Its executable state contains the authoritative schedule/channel semantics
and the optimized DAG state of every island, together with a proof that the
two agree.  Only constructors in this file can produce a state, so simulator
preparation cannot fail at runtime and a run cannot silently leave the
proved relation.
-/

namespace Loom.Hw

/-- A structurally checked System plus the ordinary Design certificate for
every island selected by its checked name lookup. -/
structure CertifiedSystem (system : System) where
  islandCertificate : ∀ (name : String) (island : SystemIsland),
    system.findIsland? name = some island → CertifiedDesign island.design
  /-- Every abstract connection has an explicit concrete refinement. This
  prevents a certified System from silently treating crossing behavior as an
  unproved implementation choice. The refinement remains technology-neutral;
  physical storage selection is a later binding. -/
  channelCertificate : ∀ (connection : SystemConnection),
    connection ∈ system.connections → Chan.Refinement connection.chan

namespace CertifiedSystem

def certificateFor {system : System} (cert : CertifiedSystem system)
    {name : String} {island : SystemIsland}
    (found : system.findIsland? name = some island) : CertifiedDesign island.design :=
  cert.islandCertificate name island found

/-! ## Exact compiler artifacts for every island -/

/-- The exact UTF-8 compiler artifact for a checked island lookup.  A caller
cannot supply a parallel Design or renderer.  System-level structural wiring
and CDC storage leaves are intentionally separate artifacts, because their
remaining contracts differ from an island's ordinary compiler theorem. -/
def renderedIslandUTF8 {system : System} (cert : CertifiedSystem system)
    {name : String} {island : SystemIsland}
    (found : system.findIsland? name = some island) : ByteArray :=
  (cert.certificateFor found).renderedUTF8

/-- Byte binding for a successfully resolved island.  This is the
`CertifiedSystem` form of `CertifiedDesign.renderedUTF8_eq`: every ordinary
per-domain Design already reaches the exact bytes consumed downstream. -/
theorem renderedIslandUTF8_eq {system : System} (cert : CertifiedSystem system)
    {name : String} {island : SystemIsland}
    (found : system.findIsland? name = some island) :
    cert.renderedIslandUTF8 found =
      (Loom.Emit.MicroVerilog.Print.print
        (Compile.compile island.design)).toUTF8 :=
  (cert.certificateFor found).renderedUTF8_eq

/-- The simulator state. `semantic` owns schedule time and abstract channel
queues. `fastIsland` is what development execution reads and updates.
`islandsAgree` is preserved by construction on every event. -/
structure State {system : System} (cert : CertifiedSystem system) where
  semantic : system.State
  fastIsland : ∀ (name : String) (island : SystemIsland),
    system.findIsland? name = some island → FastSt
  islandsAgree : ∀ (name : String) (island : SystemIsland)
    (found : system.findIsland? name = some island),
    Agree island.design (fastIsland name island found) (semantic.island name)

/-- Prepared-by-construction reset. DAG preparation success comes from the
island `CertifiedDesign` values; there is no `Option`, fallback evaluator, or
runtime certificate rejection on this path. -/
def reset {system : System} (cert : CertifiedSystem system) : cert.State where
  semantic := system.reset
  fastIsland := fun name island found => (cert.certificateFor found).simulator.reset
  islandsAgree := by
    intro name island found
    have resetAgree := FastEval.agree_fastReset island.design
    have semanticReset : system.reset.island name = island.design.reset := by
      simp [System.reset, found]
    rw [semanticReset]
    simpa [DagEval.VerifiedSimulator.reset,
      FastEval.VerifiedSimulator.reset] using resetAgree

/-- One certified schedule event. The channel/input plan is the exact public
`System` plan; only island evaluation is replaced by its proved DAG view. -/
def advance {system : System} (cert : CertifiedSystem system)
    (event : NamedClockEvent) (external : String → InEnv)
    (state : cert.State) : cert.State where
  semantic := system.advance event external state.semantic
  fastIsland := fun name island found =>
    if event.fires island.clock then
      (cert.certificateFor found).simulator.cycleOpen
        (system.islandInput event state.semantic external name)
        (state.fastIsland name island found)
    else state.fastIsland name island found
  islandsAgree := by
    intro name island found
    by_cases ticked : event.fires island.clock = true
    · have semanticStep :
          (system.advance event external state.semantic).island name =
            island.design.cycleOpen
              (system.islandInput event state.semantic external name)
              (state.semantic.island name) := by
        simp [System.advance, found, ticked]
      rw [semanticStep]
      simp only [ticked, ↓reduceIte]
      exact (cert.certificateFor found).simulator.cycleOpen_eq
        (system.islandInput event state.semantic external name)
        (state.fastIsland name island found) (state.semantic.island name)
        (state.islandsAgree name island found)
    · have unticked : event.fires island.clock = false := by simpa using ticked
      have semanticStep :
          (system.advance event external state.semantic).island name =
            state.semantic.island name := by
        simp [System.advance, found, unticked]
      rw [semanticStep]
      simp only [unticked, Bool.false_eq_true, ↓reduceIte]
      exact state.islandsAgree name island found

def runEvents {system : System} (cert : CertifiedSystem system)
    (inputs : ExternalInputs) : cert.State → List NamedClockEvent → cert.State
  | state, [] => state
  | state, event :: rest =>
      cert.runEvents inputs
        (cert.advance event (inputs state.semantic.time) state) rest

/-- Replay uses the same executable event bytes as `System.runPrefix`. -/
def runPrefix {system : System} (cert : CertifiedSystem system)
    (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : cert.State :=
  cert.runEvents inputs cert.reset events.toList

/-- The executable certified runner does not carry a second System model:
projecting its semantic component gives exactly the ordinary named-System
runner on the same replayable event list and external inputs. -/
theorem runEvents_semantic_eq {system : System} (cert : CertifiedSystem system)
    (inputs : ExternalInputs) (state : cert.State)
    (events : List NamedClockEvent) :
    (cert.runEvents inputs state events).semantic =
      system.runEventsFrom inputs state.semantic events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [runEvents, System.runEventsFrom]
      exact ih (cert.advance event (inputs state.semantic.time) state)

/-- Schedule replay is refinement-tight at the whole-System boundary.  The
fast island states remain proof-related inside the returned package, while
the authoritative semantic projection is definitionally the public runner. -/
theorem runPrefix_semantic_eq {system : System} (cert : CertifiedSystem system)
    (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) :
    (cert.runPrefix events inputs).semantic = system.runPrefix events inputs := by
  simpa [runPrefix, System.runPrefix, System.runPrefixFrom] using
    cert.runEvents_semantic_eq inputs cert.reset events.toList

/-- Fail closed before execution when the prefix violates the System's
declared clock relation. -/
def runPrefixChecked {system : System} (cert : CertifiedSystem system)
    (events : SchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : Except String cert.State :=
  if system.clockRel.accepts events then pure (cert.runPrefix events inputs)
  else throw "schedule prefix rejected by system clock relation"

/-! ## Typed state views -/

/-- Width-typed view of one register in one certified island. -/
structure RegView {system : System} (cert : CertifiedSystem system) (width : Nat) where
  islandName : String
  island : SystemIsland
  found : system.findIsland? islandName = some island
  reg : Reg width
  slot : FastEval.RegSlot island.design reg

def RegView.read {system : System} {cert : CertifiedSystem system} {width : Nat}
    (view : RegView cert width) (state : cert.State) : Nat :=
  view.slot.readNat (state.fastIsland view.islandName view.island view.found)

theorem RegView.read_eq {system : System} {cert : CertifiedSystem system} {width : Nat}
    (view : RegView cert width) (state : cert.State) :
    view.read state =
      ((state.semantic.island view.islandName).regs view.reg.name width).toNat :=
  view.slot.readNat_eq (state.islandsAgree view.islandName view.island view.found)

/-! ## Complete comparison surface -/

inductive Coord where
  | islandState (island : String) (coord : Loom.Hw.Coord)
  | channelLength (channel : String)
  | channelSlot (channel : String) (index width : Nat)
  deriving Repr, BEq

def Coord.render : Coord → String
  | .islandState island coord => island ++ "." ++ coord.render
  | .channelLength channel => "channel." ++ channel ++ ".length"
  | .channelSlot channel index _ => s!"channel.{channel}[{index}]"

/-- Derived from every island declaration and every complete bounded channel;
there is no hand-maintained comparison list. -/
def coords (system : System) (memoryCap : Nat) : List Coord :=
  system.islands.flatMap (fun island =>
    (island.design.coords memoryCap).map (.islandState island.name)) ++
  system.connections.flatMap (fun connection =>
    .channelLength connection.chan.name ::
      (List.range connection.chan.depth).map
        (fun index => .channelSlot connection.chan.name index connection.width))

def Coord.readSemantic {system : System} (state : system.State) : Coord → Nat
  | .islandState island coord => (state.island island).at coord
  | .channelLength channel => (state.channel channel).values.length
  | .channelSlot channel index _ =>
      (state.channel channel).values[index]?.map (·.toNat) |>.getD 0

/-- Every missing oracle coordinate is returned by its full derived name.
Callers must treat a nonempty result as failure. -/
def coverageGaps (system : System) (memoryCap : Nat)
    (reader : Coord → Option Nat) : List String :=
  (coords system memoryCap).filterMap fun coord =>
    if (reader coord).isNone then some coord.render else none

def requireCoverage (system : System) (memoryCap : Nat)
    (reader : Coord → Option Nat) : Except String Unit :=
  match coverageGaps system memoryCap reader with
  | [] => pure ()
  | missing => throw ("comparison coverage missing: " ++ String.intercalate ", " missing)

end CertifiedSystem
end Loom.Hw
