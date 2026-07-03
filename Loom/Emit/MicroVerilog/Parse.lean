import Loom.Emit.MicroVerilog.Ast

/-!
# The µVerilog parser (task 2.3, parse half) — WIP

Reads the exact SSA text `Print` emits back into a `Module`, so the
round-trip theorem `parse (print m) = some m` puts the text file — not just
the AST — inside the emission theorem (no trusted pretty-printer). Landing
incrementally; until `RoundTrip.lean` closes, the printed text is
corroborated by the simulator lockstep harness (`scripts/lockstep_acc8.sh`,
which passes today).
-/

namespace Loom.Emit.MicroVerilog.Wip.Parse

/-- Placeholder for the recursive-descent parser over the frozen SSA grammar.
Kept in a `Wip` namespace so the sorry policy permits it (PLAN §2). -/
def parse (_ : String) : Option Unit := none

end Loom.Emit.MicroVerilog.Wip.Parse
