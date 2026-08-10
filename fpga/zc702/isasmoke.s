; isasmoke.s -- cross-repo ISA smoke: 64-bit constant assembly + control flow,
; reduced to a checksum in r1.
;
; The generated matrix and `opdiff_rtl.sh` use lean_hw's own OP_ constants, so a
; renumbering moves the design AND the test program together and they agree by
; construction. That is the right property for the design, and it is blind to
; the question that actually broke the board: does the *assembler* -- which
; lives in the other repo, and which the guest image is built by -- still emit
; what this core decodes?
;
; So this program is written in MNEMONICS and assembled by lnp64's assembler.
; Nothing about its encoding comes from lean_hw. It then runs on the emitted RTL
; and on silicon, and the checksum is compared against the Design-derived model.
;
; The battery is the constant set from `constBattery`: zero, one, all-ones, both
; sign boundaries, and mixed high/low patterns. It is deliberately weighted
; toward LIU, because `liu` is how a 64-bit constant is built and it reached the
; bitstream with no generated program executing it at all -- which is how a -1
; ended up where a CPU count belonged.
.text
  LI   r1, 0             ; checksum accumulator
  LI   r3, 31            ; polynomial multiplier -- makes the checksum
                         ; order-sensitive, so a single wrong constant cannot be
                         ; cancelled by another wrong one

; --- constant 0: 0x0000000000000000
  LIU  r2, r0, 0
  ORI  r2, r2, 0
  MUL  r1, r1, r3
  ADD  r1, r1, r2

; --- constant 1: 0x0000000000000001
  LIU  r2, r0, 0
  ORI  r2, r2, 1
  MUL  r1, r1, r3
  ADD  r1, r1, r2

; --- constant 2: 0x00000000ffffffff  (low word all ones, high word zero)
  LIU  r2, r0, 0
  ORI  r2, r2, -1
  MUL  r1, r1, r3
  ADD  r1, r1, r2

; --- constant 3: 0xffffffffffffffff  (all ones -- the -1 that showed up where
;                                      a CPU count belonged)
  LIU  r2, r0, -1
  ORI  r2, r2, -1
  MUL  r1, r1, r3
  ADD  r1, r1, r2

; --- constant 4: 0x7fffffffffffffff  (positive sign boundary)
  LIU  r2, r0, 0x7fffffff
  ORI  r2, r2, -1
  MUL  r1, r1, r3
  ADD  r1, r1, r2

; --- constant 5: 0x8000000000000000  (negative sign boundary)
  LIU  r2, r0, -2147483648
  ORI  r2, r2, 0
  MUL  r1, r1, r3
  ADD  r1, r1, r2

; --- constant 6: 0x123456787abcdef0  (mixed, both halves non-trivial)
  LIU  r2, r0, 0x12345678
  ORI  r2, r2, 0x7abcdef0
  MUL  r1, r1, r3
  ADD  r1, r1, r2

; --- constant 7: LIU builds 0x0000ffff_00000000, then ORI's immediate is
;     SIGN-EXTENDED to 0xffffffff_ffff0000, so the result is 0xffffffffffff0000
;     and the high half LIU wrote is overwritten. That is the point: the pair is
;     here to pin ORI's sign extension, which is half of how a 64-bit constant
;     gets assembled and is invisible in any constant whose low word is positive.
  LIU  r2, r0, 0x0000ffff
  ORI  r2, r2, -65536
  MUL  r1, r1, r3
  ADD  r1, r1, r2

; --- shifts: a wrong shift and a wrong constant look alike in a single value,
;     so fold both into the same checksum.
  LSLI r4, r2, 3
  LSRI r5, r2, 7
  ASRI r6, r2, 7         ; differs from r5 iff the sign bit is respected
  MUL  r1, r1, r3
  ADD  r1, r1, r4
  MUL  r1, r1, r3
  ADD  r1, r1, r5
  MUL  r1, r1, r3
  ADD  r1, r1, r6

; --- control flow: JAL/JALR/JMP, and a taken and a not-taken branch. A decode
;     that lands on the wrong opcode here does not corrupt a value, it
;     transfers control -- which is the failure that presents as a panic rather
;     than a wrong answer.
  LI   r7, 0
  JAL  r8, sub           ; r8 = link
  ADDI r7, r7, 100       ; runs after the return
  LI   r9, 5
loop:
  ADDI r7, r7, 1
  ADDI r9, r9, -1
  BNE  r9, r0, loop      ; taken 4x, then falls through
  BEQ  r9, r0, after     ; taken
  ADDI r7, r7, 1000      ; must NOT run
after:
  MUL  r1, r1, r3
  ADD  r1, r1, r7

  SD   [r0, 0x100], r1   ; zero-page word, so dmem32 carries the checksum too
  EXIT r0

sub:
  ADDI r7, r7, 7
  JALR r0, r8, 0         ; return through the link register
