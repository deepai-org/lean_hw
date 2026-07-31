; smpcount.s -- DUAL_SPEC ladder step 2, shared test #1:
; two cores increment ONE shared DDR word N times each with an LR/SC retry
; loop. The oracle is the invariant, not a trace: [counter] == 2N.
; Both cores run this SAME image; core 1 executes a second copy at 0x4000,
; so the two text windows are disjoint and only the counter is shared.
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
  JMP  loop
done:
  LD   r10, [r1, 0]      ; final counter value (emulator-visible oracle)
  EXIT r0
