; pingpong1.s -- DUAL_SPEC ladder step 2, shared test #2 (core 1 half):
; futex ping-pong across the two cores. `turn` (first .data word, byte
; address 0x10000 = shared DDR) says whose turn it is. Core 1 runs when it
; reads 1, hands over by storing 0, and issues FUTEX_WAKE -- whose
; wake_out pulse is the OTHER core's doorbell. When it is not core 1's turn
; it FUTEX_WAITs on the same word; the wait re-reads the word and only
; blocks if it is still unchanged, so a wake that arrives early is not lost.
; r9 counts this core's turns (must be 8 at EXIT).
.data
turn: .quad 0
.text
  LI   r1, turn          ; turn word (shared DDR)
  LI   r2, 1             ; my turn value
  LI   r3, 0             ; hand-over value
  LI   r4, 8             ; turns to take
  LI   r7, 1             ; futex wake count
check:
  BEQ  r4, r0, done
  LD   r5, [r1, 0]
  BEQ  r5, r2, myturn
  FUTEX_WAIT r1, r5      ; blocks iff [r1] is still r5 (no lost wakeup)
  JMP  check
myturn:
  ADDI r9, r9, 1         ; progress counter
  SD   [r1, 0], r3       ; hand the turn over
  FUTEX_WAKE r1, r7      ; local wake + wake_out -> other core's doorbell
  ADDI r4, r4, -1
  JMP  check
done:
  EXIT r0
