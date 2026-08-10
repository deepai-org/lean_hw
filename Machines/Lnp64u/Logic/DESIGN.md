# µLog proof structure

The LNP64-µ logic is built directly over the machine's capability, lineage,
region, budget, gate, and mover state so its accounting cannot drift from the
executable specification.

The current development includes:

- well-formedness and execution-preservation lemmas;
- authority and non-interference structure;
- acyclicity, hostage-chain, and release-order arguments;
- budget and in-flight resource accounting; and
- a small separation-resource layer under `Logic/Sep/`.

Machine-wide user-facing theorems live under `Machines/Lnp64u/Theorems/`.
The release ledger, not this note, is the authoritative inventory of proved
declarations and their axiom closure.

The separation and logical-relation layer is not a blanket proof of arbitrary
adversarial programs. Claims should name the exact theorem and hypotheses;
planned stronger logical relations remain future work in `ROADMAP.md`.
