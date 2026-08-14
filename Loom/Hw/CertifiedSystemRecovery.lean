-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.CertifiedSystem
import Loom.Hw.SystemRecovery

/-!
# Certified independent-recovery System replay

The ordinary `CertifiedSystem` runner keeps every fast island state related to
the authoritative `System` semantics. Recovery must not create a second,
uncertified execution path. This module extends the same package with the
loss-explicit `RecoveryEvent` transition:

* a reset island uses the certified Design reset;
* an unaffected ticking island uses its existing certified DAG cycle, with
  inputs computed from the already-flushed intermediate System state; and
* an unaffected held island retains its fast state.

The semantic projection theorem is exact for arbitrary recovery traces.
-/

namespace Loom.Hw
namespace CertifiedSystem

/-- One certified recovery event. Reset dominates an island tick exactly as
it does in `System.advanceRecovery`; unaffected island inputs observe the
already-flushed intermediate state. -/
def advanceRecovery {system : System} (cert : CertifiedSystem system)
    (event : System.RecoveryEvent) (external : String → InEnv)
    (state : cert.State) : cert.State where
  semantic := system.advanceRecovery event external state.semantic
  fastIsland := fun name island found =>
    if event.resets name then
      (cert.certificateFor found).simulator.reset
    else if event.tick.fires island.clock then
      (cert.certificateFor found).simulator.cycleOpen
        (system.islandInput event.tick
          (system.applyRecovery event state.semantic) external name)
        (state.fastIsland name island found)
    else state.fastIsland name island found
  islandsAgree := by
    intro name island found
    cases resetEq : event.resets name with
    | true =>
        have islandName : island.name = name := System.findIsland?_name found
        have foundAtIslandName : system.findIsland? island.name = some island := by
          simpa [islandName] using found
        have resetAtIslandName : event.resets island.name = true := by
          simpa [islandName] using resetEq
        have semanticReset :
            (system.advanceRecovery event external state.semantic).island name =
              island.design.reset :=
          by
            have resetState := system.advanceRecovery_island_reset event external
              state.semantic island foundAtIslandName resetAtIslandName
            simpa [islandName] using resetState
        rw [semanticReset]
        simp only [↓reduceIte]
        simpa [DagEval.VerifiedSimulator.reset,
          FastEval.VerifiedSimulator.reset] using
            FastEval.agree_fastReset island.design
    | false =>
        have recoveredIsland :
            (system.applyRecovery event state.semantic).island name =
              state.semantic.island name := by
          simp [System.applyRecovery, resetEq]
        cases tickEq : event.tick.fires island.clock with
        | true =>
            have semanticStep :
                (system.advanceRecovery event external state.semantic).island name =
                  island.design.cycleOpen
                    (system.islandInput event.tick
                      (system.applyRecovery event state.semantic) external name)
                    (state.semantic.island name) := by
              simp [System.advanceRecovery, System.advance, resetEq, tickEq,
                found, recoveredIsland]
            rw [semanticStep]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact (cert.certificateFor found).simulator.cycleOpen_eq
              (system.islandInput event.tick
                (system.applyRecovery event state.semantic) external name)
              (state.fastIsland name island found)
              (state.semantic.island name)
              (state.islandsAgree name island found)
        | false =>
            have semanticHeld :
                (system.advanceRecovery event external state.semantic).island name =
                  state.semantic.island name := by
              simp [System.advanceRecovery, System.advance, resetEq, tickEq,
                found, recoveredIsland]
            rw [semanticHeld]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact state.islandsAgree name island found

def runRecoveryEvents {system : System} (cert : CertifiedSystem system)
    (inputs : ExternalInputs) : cert.State → List System.RecoveryEvent → cert.State
  | state, [] => state
  | state, event :: rest =>
      cert.runRecoveryEvents inputs
        (cert.advanceRecovery event (inputs state.semantic.time) state) rest

/-- Certified reset-aware replay from the common System reset. -/
def runRecoveryPrefix {system : System} (cert : CertifiedSystem system)
    (events : System.RecoverySchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : cert.State :=
  cert.runRecoveryEvents inputs cert.reset events.toList

theorem runRecoveryEvents_semantic_eq {system : System}
    (cert : CertifiedSystem system) (inputs : ExternalInputs)
    (state : cert.State) (events : List System.RecoveryEvent) :
    (cert.runRecoveryEvents inputs state events).semantic =
      system.runRecoveryEventsFrom inputs state.semantic events := by
  induction events generalizing state with
  | nil => rfl
  | cons event rest ih =>
      simp only [runRecoveryEvents, System.runRecoveryEventsFrom]
      exact ih (cert.advanceRecovery event
        (inputs state.semantic.time) state)

/-- Recovery replay has no second public semantics: projecting the certified
state yields exactly the ordinary System recovery runner on the identical
event and input trace. -/
theorem runRecoveryPrefix_semantic_eq {system : System}
    (cert : CertifiedSystem system) (events : System.RecoverySchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) :
    (cert.runRecoveryPrefix events inputs).semantic =
      system.runRecoveryPrefix events inputs := by
  simpa [runRecoveryPrefix, System.runRecoveryPrefix] using
    cert.runRecoveryEvents_semantic_eq inputs cert.reset events.toList

/-- Fail closed on both reset policy/name validity and the ordinary clock
relation before executing the certified runner. -/
def runRecoveryPrefixChecked {system : System} (cert : CertifiedSystem system)
    (events : System.RecoverySchedulePrefix)
    (inputs : ExternalInputs := fun _ _ _ _ => 0) : Except String cert.State := do
  if !events.all (system.recoveryEventOk ·) then
    throw "recovery schedule violates SystemResetPolicy or names an invalid island"
  let ticks := events.map (·.tick)
  if !system.clockRel.accepts ticks then
    throw "recovery schedule tick projection rejected by ClockRel"
  pure (cert.runRecoveryPrefix events inputs)

end CertifiedSystem
end Loom.Hw
