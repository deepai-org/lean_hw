; loomcheck.s -- lnp64mini-on-Loom cross-check: ALU/MUL/DIV/zp-mem/branch,
; results in r1..r8, read from rf after EXIT (emulator / iverilog / board).
.text
  LI   r1, 6
  LI   r2, 7
  MUL  r3, r1, r2        ; 42
  LI   r4, 255
  DIV  r5, r4, r2        ; 36
  XOR  r6, r3, r5        ; 14
  SD   [r0, 0x100], r3   ; zero-page store
  LD   r7, [r0, 0x100]   ; load back -> 42
  ADD  r8, r7, r6        ; 56
  LI   r9, 0
loop:
  ADDI r9, r9, 2
  BNE  r9, r6, loop      ; spins until r9 == 14 (branch exercise, 4-ish laps)
  EXIT r0
