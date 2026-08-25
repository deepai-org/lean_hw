# Loom

Loom is a technology-neutral hardware language in Lean 4. One typed `Design`
drives proofs, certified simulation, and Verilog; typed components and channels
cover multiclock systems.

## 1. Install

```console
git clone https://github.com/deepai-org/lean_hw.git
cd lean_hw
lake build
lake test
```

Requires [Elan](https://lean-lang.org/lean4/doc/quickstart.html), but no HDL or
FPGA tools.

## 2. Make a circuit

```lean
import Loom.Hw.Dsl
open Loom.Hw Loom.Hw.Dsl

hardware counter where
  output reg count : 8
  rule tick := count <- count + 1

#trace_cycle design with {} from { count := 41 }
#run_hardware design for 10 cycles
```

Save as `Counter.lean`; run `lake env lean Counter.lean`. Expressions read old
state; writes commit at the edge. Loom checks widths and structure.

## 3. Continue

- Language: [tutorial](TUTORIAL.md) and [syntax](PRETTY.md).
- Systems: [multiclock](MULTICLOCK.md) and [RTL import](IMPORTING_RTL.md).
- Claims: [status](STATUS.md), [reproduction](REPRODUCING.md), and [trust](TCB.md).

Proofs reach µVerilog semantics and selected exact bytes—not synthesis, timing,
physical design, external IP, or silicon.

Apache-2.0; see [LICENSE](LICENSE).
