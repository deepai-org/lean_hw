; sbcheck.s -- minimal repro probe for the renumbered-image boot failure.
; A byte store at DDR byte-lane 7 (sb [r1+63] with r1 8-aligned) must merge
; into line r1+56 and touch nothing else. The failing boot's AXI trace showed
; the RMW landing on the WRONG LINE (EA-127's line) with the lane correct.
.text
  LI   r1, 0x2a98
  LI   r2, 0x32
  SD   [r1, 56], r0      ; clean the true target line   (0x17f7ad0)
  SD   [r1, -64], r0     ; clean the observed-wrong line (0x17f7a58)
  SB   [r1, 63], r2      ; the failing shape: lane 7
  LD   r3, [r1, 56]      ; expect 0x3200000000000000
  LD   r4, [r1, -64]     ; expect 0
  LBU  r5, [r1, 63]      ; expect 0x32
  EXIT r0
