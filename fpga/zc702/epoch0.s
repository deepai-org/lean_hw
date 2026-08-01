; epoch0.s -- core 0 (referent volume 0) in the epoch demo: THE BUMPER.
; Reaches the Loom-emitted epoch engine through the existing GP MMIO
; aperture at 0x0A0E_0000 (EPOCH_SPEC.md "Core integration + demo": MMIO,
; not new opcodes, so the core's proved ladder is untouched).
;
; Word map: +0 cell, +4 epoch, +8 flags, +12 fire CHECK, +16 RESULT
;           (blocks), +20 fire BUMP (bit0 = poison), +24 latency (blocks
;           until the bump RETURNS -- Section 3's linearization point).
;
; Handshake with core 1 through the shared DDR word `flag`:
;   1 = core 1 checked the live handle and got ok
;   2 = core 0's bump has RETURNED (all volumes acked)
;   3 = core 1 re-checked the same handle and got -STALE
.data
flag: .quad 0
.text
  LI   r1, 0x0A0E0000        ; engine MMIO page
  LI   r2, flag              ; shared handshake word (DDR)
  ADDI r5, r0, 5             ; the cell under test
w1:
  LD   r3, [r2, 0]
  ADDI r4, r0, 1
  BNE  r3, r4, w1            ; wait for core 1's live check
  ; ---- the architected bump: increment, broadcast, collect acks, return
  ST.W [r1, 0], r5           ; cell = 5
  ST.W [r1, 20], r0          ; fire BUMP, policy = lazy
  LD.W r11, [r1, 24]         ; BLOCKS until the bump returns; r11 = latency
  ADDI r6, r0, 2
  ST   [r2, 0], r6           ; publish "the bump has returned"
  ; ---- volume 0's own view of the same handle
  ADDI r7, r0, 1
  ST.W [r1, 4], r7           ; presented epoch = 1 (the pre-bump one)
  ADDI r8, r0, 7
  ST.W [r1, 8], r8           ; wellFormed | classOk | rights
  ST.W [r1, 12], r0          ; fire CHECK
  LD.W r12, [r1, 16]         ; expect 0x103 = valid | -STALE
  ADDI r7, r0, 2
  ST.W [r1, 4], r7           ; presented epoch = 2 (the new one)
  ST.W [r1, 12], r0
  LD.W r13, [r1, 16]         ; expect 0x100 = valid | ok
w3:
  LD   r3, [r2, 0]
  ADDI r4, r0, 3
  BNE  r3, r4, w3            ; wait until core 1 has observed -STALE
  ; ---- poison: after this even CURRENT-epoch references fail, forever
  ST.W [r1, 0], r5
  ADDI r9, r0, 1
  ST.W [r1, 20], r9          ; fire BUMP, policy = poison
  LD.W r14, [r1, 24]         ; blocks until it returns
  ADDI r7, r0, 3
  ST.W [r1, 4], r7           ; the CURRENT epoch after two bumps
  ST.W [r1, 12], r0
  LD.W r15, [r1, 16]         ; expect 0x102 = valid | -POISONED
  EXIT r0
