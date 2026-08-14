-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.SystemRealize

/-!
# Partial SDC rendering of Loom's neutral clock constraints

SDC is one downstream flow syntax, not Loom semantics and not a generic
emission default. It is a text helper, not a complete backend: unsupported
requirements remain explicit `# REQUIRED` lines, reset intent is not lowered,
and this module cannot construct a successful `PhysicalCheckReport`. FPGA and
ASIC evidence flows may reuse it while implementing the full exact-coverage
interface; another flow can consume the same structured values directly.
-/

namespace Loom.Evidence.Constraints.Sdc

open Loom.Hw.System

def renderConstraint : TimingConstraint → String
  | .asynchronousClocks left right =>
      s!"set_clock_groups -asynchronous -group [get_clocks {left}] -group [get_clocks {right}]"
  | .maxDelay fromClock toClock nanoseconds =>
      s!"set_max_delay {nanoseconds} -from [get_clocks {fromClock}] -to [get_clocks {toClock}]"
  | .falsePath fromClock toClock =>
      s!"set_false_path -from [get_clocks {fromClock}] -to [get_clocks {toClock}]"
  | .synchronizerChain destinationClock stages =>
      s!"# REQUIRED synchronizer chain on {destinationClock}: " ++
        String.intercalate " -> " (stages.map PhysicalObject.render)
  | .coherentBus sourceClock destinationClock launch capture width maxSkew maxDelay =>
      s!"# REQUIRED coherent bus ({width} bits) {PhysicalObject.render launch} -> " ++
        s!"{PhysicalObject.render capture}, {sourceClock} to {destinationClock}; " ++
        s!"bus skew <= {maxSkew.numerator}/{maxSkew.denominator} {maxSkew.reference.describe}, " ++
        s!"datapath <= {maxDelay.numerator}/{maxDelay.denominator} {maxDelay.reference.describe}"

def render (file : ConstraintFileArtifact) : String :=
  String.intercalate "\n" <| file.groups.flatMap fun group =>
    (s!"# channel {group.key.channel}" :: group.constraints.map renderConstraint)

end Loom.Evidence.Constraints.Sdc
