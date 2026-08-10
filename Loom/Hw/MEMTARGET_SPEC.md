# Memory target profiles

Memory portability is checked against an explicit `MemTarget`, rather than a
single vendor's block-RAM rules.

`Loom/Hw/MemTarget.lean` defines the generic profile schema and checks. The
repository's concrete profiles live in `Evidence/Targets/Memory.lean` and
record, for each target:

- macro and soft-memory class names;
- maximum macro write-port count;
- minimum macro data width and depth; and
- whether macro and soft mappings can deliver an initialization image.

`realizableOnB` applies those declared capabilities to a design. The shipped
profiles are `xc7`, `ecp5`, and `asicSram`. The XC7 profile is exercised by
the repository's synthesis flow; ECP5 and generic ASIC SRAM are conservative
profiles, not claims of completed vendor or foundry qualification.

Synchronous-read discipline and independence from reset images are broadly
portable requirements. Port-count, granularity, and image delivery depend on
the selected implementation class and therefore belong in the profile.

A passing profile check means the declared memory shapes are compatible with
the model. It does not prove that synthesis selected the predicted resource,
that a foundry macro exists with identical electrical properties, or that a
synthesized implementation preserves behavior. Those are external evidence;
Loom currently provides no post-synthesis checker.
