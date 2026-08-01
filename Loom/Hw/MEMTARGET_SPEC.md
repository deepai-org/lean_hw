# Memory shape checks must be parameterized by target (D38 design decision)

Recorded 2026-08-01, before building D38, in response to a specific risk:
**shape checks that encode one vendor's block RAM make every future design
FPGA-shaped forever.** The charter's claim is that the same module targets
every FPGA vendor *and* the ASIC flow; a check hardcoding Xilinx 7-series
would quietly retire that claim.

## The checks are not all the same kind

*Universal, and in fact ASIC-correct — keep these unparameterized:*
* **Sync read (D19).** ASIC SRAM macros are synchronous-read; so is FPGA block
  RAM. Async read is the outlier (LUTRAM on FPGA, a flop array on ASIC). D19
  pushes toward the shape both technologies want.
* **No reliance on a reset image (D30/D37).** SRAM has *no* initial contents.
  This is the ASIC rule; the FPGA merely tolerated violating it. Enforcing it
  makes designs LESS FPGA-shaped.

*Vendor-specific, and the actual risk — parameterize these:*
* write-port count (D38's subject), depth/width granularity, the narrow-bank
  threshold at which a mapping falls out of block RAM, byte-enable shape.

## The decision

Introduce a declared memory-technology profile as ordinary Lean data:

    structure MemTarget where
      name            : String
      syncReadOnly    : Bool     -- refuse async reads (both real targets: true)
      maxWritePorts   : Nat      -- per memory
      initDeliverable : Bool     -- false for ASIC SRAM; false for FPGA LUTRAM
      minDepth/minWidth/granularity : Nat   -- when a bank stops being a macro
      …

and state the shape checks as **"is this design realizable on target T"**,
not "is this BRAM-friendly". Ship profiles for `xc7`, and stubs for `ecp5`
and `asicSram` written from their datasheets, so:

1. one design can be checked against several targets at once;
2. a design realizable on only one target is **visibly** target-specific
   rather than silently so;
3. the portability claim becomes a checked property instead of an assertion —
   `realizableOn xc7 d ∧ realizableOn asicSram d` is a Boolean anyone can run.

D37's image check is the first instance and should be re-expressed this way:
"non-zero image on a bank whose mapping does not deliver one" is exactly
`¬ initDeliverable` for the mapping class the target profile predicts.

## What this does not do

It does not make a design portable; it makes non-portability *visible*. And
it predicts a mapping — synthesis may still choose otherwise, which is why
eqcheck's downstream memory checks (D31) stay: prevention and detection are
complementary, and neither replaces the other.
