# Declared observability

Every `Design` has two explicit output forms:

- `outputs : List String` selects registers exported as `o_<name>` ports.
- `combOutputs : List CombOutput` declares named same-cycle expression ports.

An unselected register remains in the implementation but is absent from the
architectural port list unless a declared combinational output deliberately
reads it.

This is intentionally explicit. A design that wants to export every register
must say so, for example with `outputs := regs.map (·.name)`. Emission rejects
unknown output names.

## Proved properties

`Loom/Hw/Outputs.lean` establishes the interface property at three levels.
For a hidden register, the property explicitly requires that no declared
combinational output reads or republishes it:

- `compile_not_exported`: an unselected register is neither an output port
  nor the driver of one;
- `compile_portNames_not_exported`: it is absent from the complete module
  port-name set under the normal input-name condition; and
- `printed_not_exported`: after a successful parser round trip, the emitted
  artifact also lacks the unselected output.

The file also proves that prefixing renames both output forms, parallel
composition combines them, and connection preserves port names and widths
while substituting connected inputs into combinational values.

## Same-cycle semantics

`Design.evalCombOutput input state output` evaluates an output from the
current input valuation and pre-edge state. It takes no transition and does
not alter `Design.cycle`. `Compile.compileCombOutput_evalOpen` proves that the
compiled port expression has exactly this value for arbitrary inputs and
states. Duplicate output names and input/output name collisions are rejected
by `Design.emitCheck`.

## Security boundary

Declared observability prevents architectural disclosure across the generated
module interface. It does not make state physically secret. FPGA bitstream
readback, invasive extraction, scan structures, side channels, or a reset
constant may still reveal a value. Threat models requiring device-bound
secrets need mechanisms outside this property.

Resource effects are likewise not guaranteed: hiding ports can change
synthesis optimization in either direction. Measure cost in the actual
wrapper and tool flow.
