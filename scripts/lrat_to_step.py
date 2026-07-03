#!/usr/bin/env python3
"""UNTRUSTED translator: cadical ASCII-LRAT proof -> Loom.Dp.Cert.Check.Step list.

Mirrors `Loom/Dp/Solver.lean` (`parseLrat`) for offline certificate
generation, reusing the id->position convention of `scripts/gen_php_cert.py`.
Nothing here is trusted: the emitted certificate is re-checked by the
kernel-reducible `Check.check` (`by decide`).

Pipeline (see `Tests/Acc8Bmc.lean`):
  1. dump `bmcCnf`/`kindStepCnf` to DIMACS with a compact 1..N variable map,
     and the original `Var`-renamed ids in first-occurrence order (vars.txt);
  2. `cadical --no-binary --lrat problem.cnf proof.lrat`;
  3. `lrat_to_step.py proof.lrat vars.txt NORIG [DEFNAME] > cert.lean`.

`vars.txt` is whitespace-separated: compact id `c` denotes original id
`vars[c-1]`.  `NORIG` = number of original clauses (the CNF length).

Usage: lrat_to_step.py PROOF.lrat VARS.txt NORIG [DEFNAME]
"""
import sys


def main() -> None:
    lrat_path, vars_path, norig = sys.argv[1], sys.argv[2], int(sys.argv[3])
    defname = sys.argv[4] if len(sys.argv) > 4 else "cert"
    orig = [int(x) for x in open(vars_path).read().split()]

    def lit(tok: str) -> str:
        c = abs(int(tok))
        return f"({orig[c - 1]}, {'true' if int(tok) > 0 else 'false'})"

    steps = []
    m = 0  # clauses learned so far
    for line in open(lrat_path):
        toks = line.split()
        if len(toks) < 2 or toks[1] == "d":   # header noise / deletion line
            continue
        rest = toks[1:]                        # drop the clause id
        z = rest.index("0")
        lits = rest[:z]
        after = rest[z + 1:]
        hints = [int(h) for h in after[:after.index("0")]]

        def hpos(idv: int) -> int:
            return m + (idv - 1) if idv <= norig else m - 1 - (idv - norig - 1)

        clause = "[" + ", ".join(lit(x) for x in lits) + "]"
        hintlist = "[" + ", ".join(str(hpos(h)) for h in hints) + "]"
        steps.append(f"  .add {clause} {hintlist}")
        m += 1

    print(f"-- {len(steps)} RUP steps (untrusted; kernel-rechecked by Check.check)")
    print(f"def {defname} : List Check.Step := [")
    print(",\n".join(steps))
    print("]")


if __name__ == "__main__":
    main()
