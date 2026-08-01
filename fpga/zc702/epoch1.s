; epoch1.s -- core 1 (referent volume 1) in the epoch demo: THE OBSERVER.
; Holds one reference to cell 5 at epoch 1 and checks it twice, either
; side of core 0's bump. The engine's check unit 1 reads replica bank 1,
; which core 1 cannot write -- the -STALE verdict is established by the
; engine, never asserted by software.
.data
flag: .quad 0
.text
  LI   r1, 0x0A0E0000
  LI   r2, flag
  ADDI r5, r0, 5
  ST.W [r1, 0], r5           ; cell = 5
  ADDI r7, r0, 1
  ST.W [r1, 4], r7           ; presented epoch = 1
  ADDI r8, r0, 7
  ST.W [r1, 8], r8           ; wellFormed | classOk | rights
  ST.W [r1, 12], r0          ; fire CHECK  (before any bump)
  LD.W r9, [r1, 16]          ; expect 0x100 = valid | ok
  ADDI r6, r0, 1
  ST   [r2, 0], r6           ; tell core 0 to bump
w2:
  LD   r3, [r2, 0]
  ADDI r4, r0, 2
  BNE  r3, r4, w2            ; wait for the bump's RETURN
  ST.W [r1, 12], r0          ; fire CHECK on the SAME staged handle
  LD.W r10, [r1, 16]         ; expect 0x103 = valid | -STALE
  ADDI r6, r0, 3
  ST   [r2, 0], r6           ; release core 0 for the poison bump
  ; ---- GEM0 is still core-0-only: this GP access is NOT on the engine
  ;      page, so DUAL_SPEC D5's tie-off still answers it (done, reads 0)
  ;      and core 1 neither reaches GEM0 nor wedges.
  LI   r12, 0xE000B000
  LD.W r11, [r12, 0]         ; expect 0
  EXIT r0
