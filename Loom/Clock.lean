-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

/-!
# Technology-neutral clock-edge intent

The ordinary Loom `Design` semantics advances on an abstract tick.  Edge
polarity belongs to the boundary which maps that tick onto an HDL event, not
to the transition relation itself.  Keeping the vocabulary below the
hardware/compiler layers lets imported falling-edge domains use the same
proved `Design` and compiler as rising-edge domains.
-/

namespace Loom

inductive ClockEdge where
  | rising
  | falling
  deriving Repr, DecidableEq, BEq

namespace ClockEdge

def verilogKeyword : ClockEdge → String
  | .rising => "posedge"
  | .falling => "negedge"

end ClockEdge

end Loom
