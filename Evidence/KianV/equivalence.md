# KianV bottom-up equivalence closure

Status: **PASS**

- Reachable specializations: 74/74 covered
- Loom logic proofs: 73 PASS
- Exact technology contracts: 1 PASS (GF180 SRAM wrapper)
- Compositional proofs: 72
- Explicit flatten fallback: 1 (32-bit logarithm hierarchy)
- Memory relational-induction proofs: 4

The memory strategy packs every mapped word into an exact per-memory
state relation, asserts all related state bits plus observable ports,
and proves the zero-refinement base case and one-step invariant by
unbounded temporal induction. It does not abstract or omit memory bits.

## Bound artifacts

- Elaborated JSON: `9ef9c33b922374790c85dbfecd4e4a3900eece4b1433558e86dad8a6f57c8d18`
- Neutral package: `2a84a63d4c019b05b4ff006dec34031a696ef3892d754b9a11e3d97082703399`
- Loom-emitted RTL: `87029f94fd18ac30328ece3281410128453a42ba6f3b592a78fa04c8099ae83d`
- GF180 SRAM contract: `4afb30798e8cc1178f7fbbd506ed3229f0ffec54de2a1a3730edcec2fd60b581`

## Non-default proof cases

| Module | Result | Composition | Strategy | State relations |
|---|---:|---|---|---:|
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | PASS | compositional | memory_relational_induction | 160 |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | PASS | compositional | memory_relational_induction | 8 |
| `$paramod$9b7a6de76a656f235265b36ced3b9a85d704f591\fifo` | PASS | compositional | memory_relational_induction | 19 |
| `$paramod\Logarithm_of_Powers_of_Two\WORD_WIDTH=s32'00000000000000000000000000100000` | PASS | flatten | equiv_simple_induct | 0 |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | CONTRACT | external contract | external contract | 513 |
| `register_file` | PASS | compositional | memory_relational_induction | 32 |

The companion JSON records every specialization. Generate both files
only from a single all-green report using
`scripts/kianv_equivalence_evidence.py`; partial reports fail closed.
