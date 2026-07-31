; smpcount_skew.s -- the CONTENTION variant of smpcount.s: the loop body is
; two instructions longer, so when core 1 runs this and core 0 runs
; smpcount.s the two loops drift through every relative phase instead of
; settling into a stable non-overlapping interleaving. This is the program
; that livelocked the "kill on any remote access" reservation design
; (2,000,000 cycles / 2 increments); with the arbiter-resident conditional
; store it finishes with the invariant intact.
; `counter` is the first .data word = byte address 0x10000, which is
;   * >= 0x1000, so the mini core routes it to shared DDR (not zero page),
;   * backed by the Rust emulator's flat-exec data image, so this same
;     program runs single-core on the emulator (r10 = N there).
.data
counter: .quad 0
.text
  LI   r1, counter       ; shared counter address (DDR)
  LI   r2, 100           ; N = 100 increments for this core
  LI   r3, 1
loop:
  BEQ  r2, r0, done
retry:
  LR.D r4, r1            ; reserve the counter word
  ADD  r4, r4, r3
  SC.D r5, r4, r1        ; r5 = 0 on success, 1 on failure
  BNE  r5, r0, retry     ; lost the reservation -> re-read and retry
  ADDI r2, r2, -1
  ADDI r9, r9, 1         ; this core's committed increments (= N at the end)
  ADDI r11, r11, 1       ; padding: skews this loop against smpcount.s
  ADDI r12, r12, 1
  JMP  loop
done:
  LD   r10, [r1, 0]      ; final counter value (emulator-visible oracle)
  EXIT r0
