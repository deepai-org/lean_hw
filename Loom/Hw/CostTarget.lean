-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Cost

/-!
# Target-parameterized cost estimates

`Cost.lean` supplies the abstract vector. This module defines the generic
schema and calculations for applying an explicitly supplied calibration.
Concrete vendor, device, and process calibrations live in the external
`Evidence` library.

Two claims, kept apart on purpose:

* **Capacity** — does the predicted resource use fit the part at all?
  A hard, physical limit.
* **Closure risk** — will the selected implementation flow place, route, and
  meet timing there? A calibrated threshold, never a universal constant.

**What this does not claim.** It predicts *risk*, not place-and-route
success, and it predicts *synthesis* while the observed pain was routing.
A weight fitted on one design family transfers to another only as far as
the families resemble each other, which is why `fittedOn` is a required
field rather than a comment. A build remains the only oracle.
-/

namespace Loom.Hw

/-- Where a number came from. A profile without this is a guess wearing a
lab coat — the ECP5 `MemTarget` profile is labelled a datasheet reading
for exactly this reason. -/
inductive Provenance where
  /-- Fitted from measured tool output: which tool, which version. -/
  | measured (tool : String) (version : String)
  /-- Read off a datasheet or user guide; never validated by a run here. -/
  | datasheet (source : String)
  /-- A placeholder, deliberately conservative, awaiting measurement. -/
  | provisional
deriving Repr, BEq

def Provenance.render : Provenance → String
  | .measured t v => s!"measured ({t} {v})"
  | .datasheet s  => s!"datasheet ({s})"
  | .provisional  => "PROVISIONAL — not measured"

/-- A calibrated area/closure profile for one target.

Weights are per unit of the corresponding `Cost` dimension, in
milli-units of `resourceName` so integer arithmetic keeps the model
reproducible (no floats in a check that gates a build). -/
structure CostTarget where
  /-- Profile name, as it appears in a report (`xc7z020`, `sky130`, …). -/
  name : String
  /-- What the primary resource is called (`LUT`, `gate-equivalent`). -/
  resourceName : String
  /-- Milli-resources per state bit. -/
  wStateBits : Nat
  /-- Milli-resources per unit of combinational bit-work. -/
  wBitOps : Nat
  /-- Milli-resources per soft memory bit — the dimension that carries the
  order-of-magnitude (CE9/CE10's 14×). Macro bits cost no primary
  resource; they are reported separately as macro instances. -/
  wSoftBits : Nat
  /-- Bits per dedicated macro instance, for the separate macro report. -/
  macroBitsPerInstance : Nat
  /-- **Unit bridge.** Weights are fitted against the SYNTHESIZER's cell
  count; `capacity` is in the PLACER's site count, and packing expands one
  into the other. Two numbers both called "LUTs" is exactly the kind of
  silent unit mismatch this repo has been bitten by, so the conversion is a
  named field with its own measurement rather than an implicit factor.

  Treat this as calibrated per target and re-measure it when the design
  family changes. -/
  packExpansionMilli : Nat
  /-- **Capacity**: primary resources the part physically has. -/
  capacity : Nat
  /-- Macro instances the part physically has. -/
  macroCapacity : Nat
  /-- **Closure threshold**, in percent of `capacity`: the calibrated
  utilization above which this tool flow stops closing reliably on this
  part for this design family. Not a universal constant. -/
  closurePercent : Nat
  /-- How the weights were obtained. -/
  weightProvenance : Provenance
  /-- How `closurePercent` was obtained — usually a different, weaker
  provenance than the weights, and worth saying so. -/
  closureProvenance : Provenance
  /-- The design family the fit was taken over. A prediction outside it is
  extrapolation and the report says so. -/
  fittedOn : String
deriving Repr

namespace CostTarget

/-- Predicted synthesizer cell count (the unit the weights were fitted in). -/
def predictCells (t : CostTarget) (c : Cost) : Nat :=
  (c.stateBits * t.wStateBits + c.bitOps * t.wBitOps + c.softBits * t.wSoftBits) / 1000

/-- Predicted placer site count — cells through the packing expansion. This
is the number `capacity` and `closurePercent` are stated against. -/
def predict (t : CostTarget) (c : Cost) : Nat :=
  t.predictCells c * t.packExpansionMilli / 1000

/-- Predicted dedicated-macro instances, rounded up. -/
def predictMacros (t : CostTarget) (c : Cost) : Nat :=
  if t.macroBitsPerInstance = 0 then 0
  else (c.macroBits + t.macroBitsPerInstance - 1) / t.macroBitsPerInstance

/-- **Capacity**: does it fit at all? A hard, physical claim. -/
def fits (t : CostTarget) (c : Cost) : Bool :=
  t.predict c ≤ t.capacity && t.predictMacros c ≤ t.macroCapacity

/-- **Closure risk**: is predicted use under the calibrated threshold?
A `false` here is not "will not work" — it is "this is the region where
this flow has historically stopped closing", which is a reason to measure
before building on top, not a refusal. -/
def withinClosureBudget (t : CostTarget) (c : Cost) : Bool :=
  t.predict c * 100 ≤ t.capacity * t.closurePercent

/-- Utilization in percent, for reports. -/
def utilPercent (t : CostTarget) (c : Cost) : Nat :=
  if t.capacity = 0 then 0 else t.predict c * 100 / t.capacity

/-- A report that states capacity and closure as separate claims and never
hides its provenance. -/
def report (t : CostTarget) (c : Cost) : String :=
  let p := t.predict c
  let m := t.predictMacros c
  let u := t.utilPercent c
  s!"{t.name}: ~{p} {t.resourceName} ({u}% of {t.capacity}), {m}/{t.macroCapacity} macros\n" ++
  s!"  ({t.predictCells c} synthesizer cells x {t.packExpansionMilli}/1000 packing)\n" ++
  s!"  capacity: {if t.fits c then "fits" else "DOES NOT FIT"}\n" ++
  s!"  closure:  {if t.withinClosureBudget c then "within" else "ABOVE"} the " ++
  s!"{t.closurePercent}% calibrated threshold\n" ++
  s!"  weights:  {t.weightProvenance.render}, fitted on {t.fittedOn}\n" ++
  s!"  closure threshold: {t.closureProvenance.render}\n" ++
  s!"  estimate predicts RISK, not P&R success; a build is the only oracle."

end CostTarget

end Loom.Hw
