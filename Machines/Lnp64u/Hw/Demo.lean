import Machines.Lnp64u.Iss

/-!
# LNP64-µ system-op demo manifest (task 1.11)

The configuration the system-op lockstep test (`Tests/Lnp64uCore.lean`) and
the `lnp64u` emission target both run: four domains exercising **every**
system opcode —

* d0 (orchestrator): `cap_dup` (narrow + errno paths), `map`/`unmap`,
  `cap_drop` (reparent + orphan branches, region sweep), stale-handle
  reuse, `mem_grant` (cross-domain), a `cap_revoke` of a derivation tree
  with a cross-domain grant *while the Mover runs under a doomed
  descendant* (abort + `-ESTALE` status), a completing Mover job
  (same-cycle final word + status), `gate_call` with capability transfer
  and reply, donation drain (forced unwind), callee `halt` unwind,
  `moverBusy`/`gateBusy` errnos, `yield`.
* d1: gate-0 callee — maps the transferred capability, writes through it,
  makes a *nested* gate call (chain depth 2, three-hop payer walk), dups a
  reply, returns it; `halt`s when called without a capability.
* d2: mailbox-synchronized grant recipient — maps the granted capability,
  reads through it, and (after the revoke) faults on the swept region.
* d3: sacrificial donation-drain callee (spins until forcibly unwound).
-/

namespace Machines.Lnp64u.Demo

open Machines.Lnp64u

/-- Root-capability handle of slot `s` at generation 1. -/
def rootH (s : Nat) (gate : Bool := false) : BitVec 17 :=
  BitVec.ofNat 17 (s + 16 + if gate then 4096 else 0)

/-- Pack a `cap_dup`/`mem_grant` descriptor word. -/
def desc (tgt : Nat) (r w x : Bool) (off len : Nat) : Loom.Word32 :=
  BitVec.ofNat 32 <|
    tgt + (if r then 4 else 0) + (if w then 8 else 0) + (if x then 16 else 0)
    + (off <<< 5) + (len <<< 17)

/-! Memory map (words): code d0 `0x100` (128), d1 `0x200` (64, gate-0
handler `0x210`, halt `0x220`), d2 `0x280` (64, gate-2 handler `0x2A0`),
d3 `0x2C0` (16); data d0 `0x400` (256, consts at `0x430`, stash `0x420`),
mailbox `0x500` (16), data d2 `0x520` (32), data d1 `0x540` (32, const
`0x550`), grant pool `0x600` (256, marker at `0x600`), bulk `0x700` (256).
-/

/-- d0: the orchestrator (see module docstring; stash cells `0x424`–`0x42E`
hold the golden results). -/
def prog0 : List Loom.Word32 :=
  [ ins "addi" 7 0 0 0x400
  -- phase 1: dup → map → store → drop-while-mapped (region sweep) → stale
  , ins "lw"   1 7 0 0x34          --  1: desc1 (dup data: off 0x10 len 8 rw)
  , ins "addi" 2 0 0 (rootH 1)     --  2: data cap handle
  , ins "cap_dup" 3 2 1 0          --  3: C
  , ins "map"  4 3 0 2             --  4: region2 := C
  , ins "addi" 5 0 0 1234
  , ins "sw"   0 7 5 0x10          --  6: mem[0x410] := 1234
  , ins "cap_drop" 4 3 0 0         --  7: drop C (region2 swept)
  , ins "cap_dup" 4 3 1 0          --  8: stale parent → -1
  , ins "sw"   0 7 4 0x26
  , ins "cap_dup" 3 2 1 0          -- 10: re-derive
  , ins "map"  4 3 0 2
  , ins "unmap" 4 0 0 2
  , ins "cap_drop" 4 3 0 0         -- 13: tidy (reparent branch)
  -- phase 2: errno paths
  , ins "lw"   1 7 0 0x35          -- 14: descBadPerm (rwx from rw)
  , ins "cap_dup" 4 2 1 0          -- 15: → -7
  , ins "sw"   0 7 4 0x28
  , ins "lw"   1 7 0 0x36          -- 17: descRange (250+20 > 256)
  , ins "cap_dup" 4 2 1 0          -- 18: → -3
  , ins "sw"   0 7 4 0x29
  , ins "addi" 1 0 0 (rootH 4 true)  -- 20: gate3 (callee = d0)
  , ins "gate_call" 4 1 0 0        -- 21: self-callee → -6
  , ins "sw"   0 7 4 0x2A
  -- phase 4: a completing Mover job (4 words, consts → 0x480)
  , ins "lw"   1 7 0 0x3A          -- 23: descSrc (off 0x30 len 8 r)
  , ins "cap_dup" 3 2 1 0
  , ins "lw"   1 7 0 0x3B          -- 25: descDst (off 0x80 len 8 rw)
  , ins "cap_dup" 4 2 1 0
  , ins "sw"   0 7 3 0x20          -- 27: descriptor: src handle
  , ins "sw"   0 7 4 0x21          --     dst handle
  , ins "addi" 5 0 0 4
  , ins "sw"   0 7 5 0x22          --     count 4
  , ins "addi" 5 0 0 0x425
  , ins "sw"   0 7 5 0x23          --     status addr 0x425
  , ins "addi" 1 0 0 0x420
  , ins "move" 5 1 0 0             -- 34: mover starts (first word same cycle)
  , ins "sw"   0 7 1 0x27          -- 35: store while the mover runs
  , ins "lw"   5 7 0 0x25          -- 36: poll status
  , ins "beq"  0 5 0 (-1)          -- 37: until 1
  -- phase 5: gates (transfer + reply, drain, callee halt)
  , ins "lw"   1 7 0 0x3C          -- 38: descX (off 0x40 len 16 rw)
  , ins "cap_dup" 3 2 1 0          -- 39: X
  , ins "map"  4 3 0 3             -- 40: region3 := X (transfer must sweep)
  , ins "addi" 1 0 0 (rootH 2 true)  -- 41: gate0
  , ins "gate_call" 5 1 3 0        -- 42: transfer X to d1; r5 := reply
  , ins "map"  4 5 0 3             -- 43: region3 := reply
  , ins "lw"   4 7 0 0x40          -- 44: read 777 (d1 wrote through X)
  , ins "sw"   0 7 4 0x2C
  , ins "addi" 1 0 0 (rootH 3 true)  -- 46: gate1 (callee d3)
  , ins "gate_call" 5 1 0 0        -- 47: donation drain → -9
  , ins "sw"   0 7 5 0x2D
  , ins "addi" 1 0 0 (rootH 2 true)  -- 49: gate0, arg 0 → d1 halts
  , ins "gate_call" 5 1 0 0        -- 50: → -9 (unwind)
  , ins "sw"   0 7 5 0x2E
  -- phase 3: grant + revoke tree + in-flight Mover abort
  , ins "addi" 2 0 0 (rootH 6)     -- 52: pool
  , ins "lw"   1 7 0 0x37          -- 53: descA (len 208 rw)
  , ins "cap_dup" 3 2 1 0          -- 54: A
  , ins "lw"   1 7 0 0x38          -- 55: descB (len 200 r)
  , ins "cap_dup" 4 3 1 0          -- 56: B (child of A)
  , ins "lw"   1 7 0 0x39          -- 57: descG (target d2, len 16 r)
  , ins "mem_grant" 5 3 1 0        -- 58: G → d2 slot 3
  , ins "addi" 1 0 0 (rootH 5)     -- 59: mailbox cap
  , ins "map"  5 1 0 2             -- 60: region2 := mailbox
  , ins "addi" 6 0 0 0x500
  , ins "addi" 5 0 0 1
  , ins "sw"   0 6 5 0             -- 63: go flag
  , ins "lw"   5 6 0 1             -- 64: poll d2's ack …
  , ins "blt"  0 0 5 3             -- 65: … got it → 68
  , ins "yield" 5 0 0 0            -- 66: yield the period (else d2 starves:
  , ins "beq"  0 0 0 (-3)          -- 67:  a stalling high-prio poller holds
                                   --      the core, `Step.corePhase`)
  , ins "sw"   0 7 4 0x20          -- 68: descriptor: src = B
  , ins "addi" 5 0 0 (rootH 7)     -- 67: bulk
  , ins "sw"   0 7 5 0x21
  , ins "addi" 5 0 0 200
  , ins "sw"   0 7 5 0x22          --     count 200
  , ins "addi" 5 0 0 0x424
  , ins "sw"   0 7 5 0x23          --     status addr 0x424
  , ins "addi" 1 0 0 0x420
  , ins "move" 5 1 0 0             -- 76: long mover starts
  , ins "move" 5 1 0 0             -- 77: → -8 (moverBusy)
  , ins "sw"   0 7 5 0x2B
  , ins "cap_revoke" 5 3 0 0       -- 79: kill B + G, abort the mover
  , ins "addi" 5 0 0 1
  , ins "sw"   0 6 5 2             -- 81: mailbox[2] := 1 (d2 phase 2)
  -- phase 6: orphan drop, yield, spin
  , ins "cap_drop" 5 2 0 0         -- 82: drop pool root → A orphaned
  , ins "yield" 5 0 0 0
  , ins "beq"  0 0 0 0 ]           -- 84: spin

/-- d0's spin address (golden check). -/
def prog0Spin : Nat := 0x100 + 84

/-- d1 main: spin (activations hijack the pc). -/
def prog1Main : List Loom.Word32 := [ ins "beq" 0 0 0 0 ]

/-- d1 gate-0 handler (entry `0x210`): `r1 = 0` → halt (unwind test); else
map the transferred cap, write 777 through it, nested-call gate 2 (d2),
dup a reply from the transferred cap, return it. -/
def prog1Handler : List Loom.Word32 :=
  [ ins "beq"  0 1 0 16            -- 0x210: r1 == 0 → 0x220 (halt)
  , ins "map"  2 1 0 2             -- 0x211: region2 := X
  , ins "addi" 4 0 0 777
  , ins "addi" 5 0 0 0x440
  , ins "sw"   0 5 4 0             -- 0x214: mem[0x440] := 777
  , ins "addi" 6 0 0 (rootH 2 true)  -- 0x215: gate2 (callee d2)
  , ins "gate_call" 5 6 0 0        -- 0x216: nested call, depth 2
  , ins "addi" 6 0 0 0x540
  , ins "lw"   2 6 0 0x10          -- 0x218: descReply (at 0x550)
  , ins "cap_dup" 3 1 2 0          -- 0x219: reply = dup(X, r)
  , ins "gate_return" 4 3 0 0 ]    -- 0x21A: reply → d0

def prog1Halt : List Loom.Word32 := [ ins "halt" 0 0 0 0 ]  -- 0x220

/-- d2 main: wait for the go flag, map the granted cap (predictable handle:
slot 3, generation 1), read the marker through it, stash it, ack, wait for
the revoke signal, then read again — the swept region faults. -/
def prog2 : List Loom.Word32 :=
  [ ins "addi" 7 0 0 0x500
  , ins "lw"   1 7 0 0
  , ins "beq"  0 1 0 (-1)          -- poll go flag
  , ins "addi" 1 0 0 (rootH 3)     -- granted handle (slot 3, gen 1)
  , ins "map"  2 1 0 3             -- region3 := G
  , ins "addi" 4 0 0 0x600
  , ins "lw"   3 4 0 0             -- marker through G
  , ins "addi" 5 0 0 0x520
  , ins "sw"   0 5 3 0             -- data2[0] := marker
  , ins "addi" 6 0 0 1
  , ins "sw"   0 7 6 1             -- ack
  , ins "lw"   6 7 0 2
  , ins "beq"  0 6 0 (-1)          -- poll revoke signal
  , ins "lw"   6 4 0 0 ]           -- swept region → memoryAuthority fault

/-- d2 gate-2 handler (entry `0x2A0`): return immediately, no reply. -/
def prog2Handler : List Loom.Word32 := [ ins "gate_return" 2 0 0 0 ]

/-- d3: spin (both its boot thread and the gate-1 drain victim). -/
def prog3 : List Loom.Word32 := [ ins "beq" 0 0 0 0 ]

/-- The Mover-source payload and descriptor constants (d0 data, `0x430`). -/
def consts0 : List Loom.Word32 :=
  [ 111, 222, 333, 444                       -- 0x430: mover payload
  , desc 0 true true false 0x10 8            -- 0x434: desc1
  , desc 0 true true true 0x10 8             -- 0x435: descBadPerm
  , desc 0 true true false 250 20            -- 0x436: descRange
  , desc 0 true true false 0 208             -- 0x437: descA
  , desc 0 true false false 0 200            -- 0x438: descB
  , desc 2 true false false 0 16             -- 0x439: descG
  , desc 0 true false false 0x30 8           -- 0x3A → 0x43A: descSrc
  , desc 0 true true false 0x80 8            -- 0x43B: descDst
  , desc 0 true true false 0x40 16 ]         -- 0x43C: descX

/-- The system-op demo manifest. -/
def sysManifest : Manifest where
  doms := fun d =>
    { priority := [10, 8, 6, 4].getD d.val 0
      budgetQ := [24, 12, 10, 6].getD d.val 0
      periodP := 64
      maxDonation := [56, 20, 16, 16].getD d.val 16
      entry := BitVec.ofNat 12 ([0x100, 0x200, 0x280, 0x2C0].getD d.val 0)
      initCaps := fun s =>
        let mem (b l : Nat) (r w x : Bool) : Option CapKind :=
          some (.mem (BitVec.ofNat 12 b) (BitVec.ofNat 13 l) ⟨r, w, x⟩)
        match d.val, s.val with
        | 0, 0 => mem 0x100 128 true false true   -- code0
        | 0, 1 => mem 0x400 256 true true false   -- data0
        | 0, 2 => some (.gate 0)
        | 0, 3 => some (.gate 1)
        | 0, 4 => some (.gate 3)
        | 0, 5 => mem 0x500 16 true true false    -- mailbox
        | 0, 6 => mem 0x600 256 true true false   -- grant pool
        | 0, 7 => mem 0x700 256 true true false   -- bulk (mover dst)
        | 1, 0 => mem 0x200 64 true false true    -- code1
        | 1, 1 => mem 0x540 32 true true false    -- data1
        | 1, 2 => some (.gate 2)
        | 2, 0 => mem 0x280 64 true false true    -- code2
        | 2, 1 => mem 0x500 16 true true false    -- mailbox
        | 2, 2 => mem 0x520 32 true true false    -- data2
        | 3, 0 => mem 0x2C0 16 true false true    -- code3
        | _, _ => none
      initRegions := fun r =>
        match d.val, r.val with
        | 0, 0 => some 0 | 0, 1 => some 1
        | 1, 0 => some 0 | 1, 1 => some 1
        | 2, 0 => some 0 | 2, 1 => some 1 | 2, 2 => some 2
        | 3, 0 => some 0
        | _, _ => none }
  gates := fun g =>
    { callee := [1, 3, 2, 0].getD g.val 0
      entry := BitVec.ofNat 12 ([0x210, 0x2C0, 0x2A0, 0x100].getD g.val 0) }
  rom := romOf
    [ (0x100, prog0), (0x200, prog1Main), (0x210, prog1Handler)
    , (0x220, prog1Halt), (0x280, prog2), (0x2A0, prog2Handler)
    , (0x2C0, prog3), (0x430, consts0)
    , (0x550, [desc 0 true false false 0 16])   -- d1's descReply
    , (0x600, [48879]) ]                        -- grant-pool marker

end Machines.Lnp64u.Demo
