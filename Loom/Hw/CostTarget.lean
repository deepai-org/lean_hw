-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Cost

/-!
# W6 — calibration: from the cost vector to a target's resources and risk

`Cost.lean` is exact and technology-free. Everything here is **empirical
metadata**: fitted weights, a capacity, and a closure threshold, each
carrying the provenance that makes it auditable — which tool at which
version, on which part, fitted over which design family.

Two claims, kept apart on purpose:

* **Capacity** — does the predicted resource use fit the part at all?
  A hard, physical limit.
* **Closure risk** — will the tools actually place, route and meet timing
  there? A *calibrated threshold*, never a universal constant. On this
  repo's own evidence it sits far below capacity: the lnp64mini dual top
  at 48 % of the xc7z020's LUTs routed first try at 30.43 MHz, while the
  epoch top at 52 % burned nine hours across two seeds without routing
  (fpga_dev.md §69). The same shape governs an ASIC flow, where nobody
  targets 95 % placement density either.

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
  into the other (measured 44 646 → 56 290 SLICE_LUTX, i.e. 1.26×, on the
  epoch top). Two numbers both called "LUTs" is exactly the kind of silent
  unit mismatch this repo has been bitten by, so the conversion is a named
  field with its own measurement rather than an implicit factor. -/
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

/-- **xc7z020 (ZC702)**, the part this repo actually builds on.

Weights fitted by `scripts/fit_cost.py` over measured yosys cell counts;
the fit is UNDERDETERMINED (three weights, two designs) and says so in its
provenance, so a report cannot pass it off as settled. More designs
tighten it; nothing else does.

The closure threshold is the two data points the campaign paid for: the
dual top routed first try at 30.43 MHz, the epoch top did not route across
two seeds and nine hours (fpga_dev.md §69). Note what the model then says
about them — **both land at 52-53 %, above the threshold**. The abstract
cost vector does *not* separate the design that routed from the one that
did not; they differ by ~1 % in cells. That is the honest result, and it
is the argument for calling this a risk signal rather than a verdict: at
this margin the discriminator is congestion, not capacity. -/
def xc7z020 : CostTarget where
  name := "xc7z020"
  resourceName := "LUT"
  -- Fitted by scripts/fit_cost.py against measured yosys cell counts for
  -- lnp64mini_dual (44 112) and lnp64mini_epoch (44 646); worst residual
  -- 1.0%. wStateBits fits to 0 because state lands in flip-flops, which are
  -- not the scarce resource here — the model saying so is a small check that
  -- it is measuring the right thing.
  wStateBits := 0
  wBitOps := 7
  wSoftBits := 400
  macroBitsPerInstance := 36864
  packExpansionMilli := 1260
  capacity := 106400
  macroCapacity := 140
  closurePercent := 50
  weightProvenance := .measured "yosys 0.38 (openXC7), SLICE_LUTX" "2 designs — UNDERDETERMINED fit (3 weights), worst residual 1.0%"
  closureProvenance := .measured "nextpnr-xilinx (openXC7)" "2026-08 campaign: dual routed at 48-52%, epoch failed 2 seeds at 52-53%"
  fittedOn := "lnp64mini family only; another family is extrapolation"

/-- A generic ASIC standard-cell profile, in gate-equivalents. Datasheet
shape only: no ASIC flow has been run in this repo, and the profile says
so rather than implying a measurement that does not exist. -/
def asicGE : CostTarget where
  name := "asicGE"
  resourceName := "gate-equivalent"
  wStateBits := 5000
  wBitOps := 1500
  wSoftBits := 6000
  macroBitsPerInstance := 0
  packExpansionMilli := 1000
  capacity := 0
  macroCapacity := 0
  closurePercent := 70
  weightProvenance := .datasheet "standard-cell rules of thumb (FF ≈ 5 GE, 2-input gate ≈ 1 GE)"
  closureProvenance := .datasheet "typical placement-density practice, 60-80%"
  fittedOn := "nothing in this repo — no ASIC flow has been run here"

end Loom.Hw
