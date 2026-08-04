# Declared observability

Every `Design` has a mandatory `outputs : List String`. Only named registers
become module outputs; internal registers remain present in the implementation
but are absent from the architectural port list.

This is intentionally explicit. A design that wants to export every register
must say so, for example with `outputs := regs.map (·.name)`. Emission rejects
unknown output names.

## Proved properties

`Loom/Hw/Outputs.lean` establishes the interface property at three levels:

- `compile_not_exported`: an unselected register is neither an output port
  nor the driver of one;
- `compile_portNames_not_exported`: it is absent from the complete module
  port-name set under the normal input-name condition; and
- `printed_not_exported`: after a successful parser round trip, the emitted
  artifact also lacks the unselected output.

The file also proves that prefixing renames selections, parallel composition
combines them safely, and connection cannot republish a hidden register.

## Security boundary

Declared observability prevents architectural disclosure across the generated
module interface. It does not make state physically secret. FPGA bitstream
readback, invasive extraction, scan structures, side channels, or a reset
constant may still reveal a value. Threat models requiring device-bound
secrets need mechanisms outside this property.

Resource effects are likewise not guaranteed: hiding ports can change
synthesis optimization in either direction. Measure cost in the actual
wrapper and tool flow.
