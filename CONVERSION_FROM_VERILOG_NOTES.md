# Notes from building the Verilog-to-Loom path

## What translated cleanly

- Loom's small typed `Design` and expression tree are a good target after a
  frontend has made widths, signedness, reset values, and priority explicit.
- The existing compiler theorem remains reusable: imported logic lowers into
  the same ordinary graph as authored Loom, rather than a parallel foreign
  semantics.
- Explicit child-instance records fit the existing component/hierarchy model.
- Yosys JSON is useful as an untrusted normalization boundary because it makes
  inferred cells and parameterized modules inventoryable.

## What did not translate cleanly

- Source SystemVerilog syntax is not itself the semantic boundary. Generate
  elaboration, parameters, process priority, inferred memories, and reset
  inference must be made explicit before Loom can check them.
- A single fixed `posedge clk`/active-high `rst` emitter was insufficient.
  KianV includes falling-edge logic and commonly uses non-default reset names
  or polarity, so those became explicit AST metadata with round-trip coverage.
- Combinational-only modules do not naturally fit Loom's current always-clocked
  module frame.
- Inferred SRAMs and resetless flops need semantics and target contracts, not
  textual substitutions.
- Hierarchy preservation and behavioral equivalence are different claims. A
  readable structural wrapper is useful, but still needs exact child artifacts
  and external equivalence/signoff evidence.

## Practical rule

Never replace an unsupported cell with a guessed constant or omit an instance.
Retain a source-located blocker, improve the neutral IR/lowering deliberately,
then require original-vs-emitted equivalence again.
