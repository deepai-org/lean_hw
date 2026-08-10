; divcheck.s -- the exact wide-operand division strtoll performs, standalone.
;
; The renumbered image panicked on silicon with numcpu = LLONG_MAX (printed
; as -1 through %d), which is strtoll's ERANGE path -- taken only if
; cutoff/cutlim, computed from LLONG_MAX and 10, came out wrong. The generated
; matrices drive DIV/SREM/MULH with tiny operand vectors; nothing anywhere runs
; a full-width dividend on SILICON. This program does exactly that, in
; mnemonics through the other repo's assembler, results in distinct registers
; and a fold into r1 for the standard checksum readout.
.text
  LI   r1, 0             ; checksum accumulator
  LI   r2, 31            ; polynomial multiplier

; A = LLONG_MAX = 0x7fffffffffffffff
  LI   r10, -1
  LIU  r10, r10, 0x7fffffff
; B = 10
  LI   r11, 10
; M = strtoll's reciprocal shape 0x6666666666666667
  LI   r12, 0x66666667
  LIU  r12, r12, 0x66666666

  DIV  r3, r10, r11      ; expect 0x0ccccccccccccccc
  SREM r4, r10, r11      ; expect 7
  MULH r5, r10, r12      ; expect 0x3333333333333333
  MULHU r6, r10, r12     ; expect 0x3333333333333333
  UDIV r7, r10, r11      ; expect 0x0ccccccccccccccc
  UREM r8, r10, r11      ; expect 7

; negative dividend, truncating semantics
  LI   r13, -9
  DIV  r9, r13, r11      ; expect 0
  SREM r14, r13, r11     ; expect -9

  MUL  r1, r1, r2
  ADD  r1, r1, r3
  MUL  r1, r1, r2
  ADD  r1, r1, r4
  MUL  r1, r1, r2
  ADD  r1, r1, r5
  MUL  r1, r1, r2
  ADD  r1, r1, r6
  MUL  r1, r1, r2
  ADD  r1, r1, r7
  MUL  r1, r1, r2
  ADD  r1, r1, r8
  MUL  r1, r1, r2
  ADD  r1, r1, r9
  MUL  r1, r1, r2
  ADD  r1, r1, r14

; Keep the store byte exercised end to end, not merely the arithmetic result.
  SD   [r0, 0x100], r1
  EXIT r0
