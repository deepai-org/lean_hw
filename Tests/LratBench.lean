import Loom.Dp.Cert.Lrat

/-!
# LRAT kernel-reduction benchmark (task 0.10, decision D2)

Pigeonhole 4→3 (12 vars, 22 clauses) with a cadical-produced LRAT proof
(15 steps), embedded as terms and discharged by plain `decide` — pure
kernel reduction, no `native_decide` (Rule 1). Elapsed time for this file
is the D2 data point (recorded in PLAN.md).
-/

namespace Tests.LratBench

def phpCnf : Loom.Dp.Cert.Cnf := [
  [(0, true), (1, true), (2, true)],
  [(3, true), (4, true), (5, true)],
  [(6, true), (7, true), (8, true)],
  [(9, true), (10, true), (11, true)],
  [(0, false), (3, false)],
  [(0, false), (6, false)],
  [(0, false), (9, false)],
  [(3, false), (6, false)],
  [(3, false), (9, false)],
  [(6, false), (9, false)],
  [(1, false), (4, false)],
  [(1, false), (7, false)],
  [(1, false), (10, false)],
  [(4, false), (7, false)],
  [(4, false), (10, false)],
  [(7, false), (10, false)],
  [(2, false), (5, false)],
  [(2, false), (8, false)],
  [(2, false), (11, false)],
  [(5, false), (8, false)],
  [(5, false), (11, false)],
  [(8, false), (11, false)]
]

def phpCert : Loom.Dp.Cert.LratCert := #[
  .addRup 23 #[(-11 : Int), (-12 : Int)] #[22, 19, 13, 16, 1, 3, 6],
  .addRup 24 #[(-7 : Int), (-12 : Int)] #[21, 19, 6, 8, 1, 2, 11],
  .addRup 25 #[(-12 : Int)] #[19, 21, 22, 24, 3, 12, 14, 1, 2, 5],
  .addRup 26 #[(-8 : Int)] #[25, 12, 14, 16, 4, 7, 9, 1, 2, 17],
  .addRup 27 #[(-7 : Int)] #[25, 6, 8, 10, 4, 13, 15, 1, 2, 17],
  .addRup 28 #[(9 : Int)] #[27, 26, 3],
  .addRup 29 #[(-3 : Int)] #[28, 18],
  .addRup 30 #[(-6 : Int)] #[28, 20],
  .addRup 31 #[(-1 : Int)] #[30, 25, 5, 7, 2, 4, 15],
  .addRup 32 #[(2 : Int)] #[31, 29, 1],
  .addRup 33 #[(-5 : Int)] #[32, 11],
  .addRup 34 #[(-11 : Int)] #[32, 13],
  .addRup 35 #[(4 : Int)] #[33, 30, 2],
  .addRup 36 #[(10 : Int)] #[34, 25, 4],
  .addEmpty 37 #[35, 36, 9]
]

/- D2 finding (2026-07-03): `Std.Tactic.BVDecide.LRAT.check` is NOT
kernel-reducible (its well-founded recursion sticks under `decide`/`rfl`),
so certificates cannot be discharged by kernel reduction of the core
checker. Consequence: Loom needs an in-house, structurally-recursive,
kernel-reducible LRAT checker (task 1.2a) — core's stays as untrusted
cross-validation. Until then this file smoke-tests the pipeline
(cadical → LRAT text → parse → check) under compiled evaluation. -/
#eval do
  unless Loom.Dp.Cert.checkLrat phpCert phpCnf do
    throw (IO.userError "LRAT pipeline smoke test failed")
  IO.println "LRAT pipeline smoke test passed (compiled evaluation)"

end Tests.LratBench
