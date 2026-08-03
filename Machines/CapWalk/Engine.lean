-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Semantics
import Loom.Hw.FastEval
import Loom.Hw.SyncRead
import Loom.Hw.Compile
import Loom.Hw.CompileCorrect
import Loom.Emit.MicroVerilog.Print
import Loom.Hw.EmitIO

/-!
# `capwalk` — the LNP64 §2.2 capability cache + walker + authenticated fill (Layer 2)

Layer 1 is `Machines/CapWalk/Protocol.lean` (frozen). This is the hardware
that Layer 3 will refine to it. `CAPWALK_SPEC.md` §Layers item 2 fixes the
shape:

> hot cache (on-chip, the checking interface) + walker + fill sequencer.
> Per the doctrine: **the safety-critical check runs against on-chip state;
> DDR holds re-validatable bulk behind the fill contract.** The engine owns
> the cache and the tags; software may only present handles.

and `EPOCH_SPEC.md` §SUPERSEDING DOCTRINE fixes what "behind the fill
contract" has to mean: the contract is not a hypothesis about DDR, it is a
**check the engine performs**, so the eventual safety theorem is
unconditional over all `m_done`/`m_rdata` traces.

## Structure

```
        on-chip, never spills                spilled, re-validated on fill
   cell_epoch[2^sw] : ew                     DDR table at tbl_base
   cell_flags[2^sw] : 3   (vacant/dead/fault)      slot -> (P0, P1, TAG)
   lin_repl [2^lw] : ew   (§3 replica)                     |
          |     |                                          |
   check unit (5-step §2.2 check)  --miss-->  walker/fill sequencer
          |                                       |  m_start_rd/m_addr (out)
   c_tag/c_p0/c_p1[2^cw]  <--install--  MAC(P0‖P1‖slot‖embedded epoch)
          |                                       ^ m_done/m_rdata (D15 in)
   resp_valid/resp_code                    mismatch -> FAULT: poison the slot
```

* **Check unit** (§2.2's five steps, in §2.2's order): `Protocol.outcome`'s
  ordered spine as one mux cone over the *cached* entry and the *on-chip*
  cell — one compare, no fabric transaction. Steps 1–2 (occupancy, embedded
  epoch) are answered from `cell_*` alone, so a stale handle never causes a
  DDR transaction at all; only steps 3–5 need the entry, and only those can
  miss.
* **Walker / fill sequencer** (Appendix F row 2's "page-walker-class
  sequencer"): three single-beat reads through the HP-master handshake
  (`m_start_rd`/`m_addr` out, `m_done`/`m_rdata` in — the same shape the
  mini core's `Machines/Lnp64mini/HpMaster` presents), then a 5-round keyed
  hash, then install-or-fault.
* **Authentication** (§Authentication below): the backing entry's tag is
  bound to `{payload, slot, embedded epoch}`, and the embedded epoch is the
  one field that **never spills** (deviation C1). Corruption, substitution
  and cross-epoch replay are therefore all the *same* check.
* **Lineage** is not re-implemented: `lin_repl` is a §3 replica bank written
  only by the epoch engine's broadcast (`inval_valid/cell/epoch`), so
  `cap_revoke` is a §3 bump on the epoch engine and this engine is a
  referent volume of it (deviation CE7).

## Authentication (the scheme, and its stated assumption)

The tag over slot `s` is

```
  h0 = mix(IV, P0[31:0],  K0)
  h1 = mix(h0, P0[63:32], K1)
  h2 = mix(h1, P1,        K2)      -- P1 = the lineage stamp epoch
  h3 = mix(h2, s,         K3)      -- SLOT binding      -> substitution
  h4 = mix(h3, E(s),      K4)      -- EPOCH binding     -> replay
  TAG = h4
  mix(h,w,k) = xorshift32( h ^ w ^ k ),  xorshift32(y) = y^=y<<13; y^=y>>17; y^=y<<5
```

`E(s)` is the **on-chip** embedded epoch of slot `s` at fill time; `K0..K4`
and `IV` are engine-owned **registers** (`keyRegs`) that no rule writes and
that the design's D39 `outputs` selection keeps off the interface — they are
at no port and in no memory, so no core can read or write them. They were
bitstream *literals* until D39 landed, because every register used to emit an
`o_*` port; that was deviation CE5, now retired. The reset image of those
registers is still a compiled-in constant, so the secrecy claim remains
architectural (no interface exposure), never physical (a bitstream readback
still recovers it).

**Stated assumption (this is the honest part).** `xorshift32` is a
bijection, not a PRF. What is claimed here is *architectural*, not
cryptographic:

1. **Detection is structural.** Every one of the three attacks changes an
   input of the tag computation: corruption changes `P0`/`P1`, substitution
   changes `s`, replay changes `E(s)`. Because `mix` is injective in its
   message word for fixed `h,k`, any single-word change propagates to a
   different `h4` — so all three are detected *with certainty*, not with
   high probability, under a single-word substitution. Multi-word forgeries
   are only as hard as inverting the (public) mixing function given the
   secret round keys, which is **not** a cryptographic claim.
2. **Fail-stop is architectural.** There is exactly one code path in this
   design that writes `c_tag`/`c_p0`/`c_p1`, and it is guarded by
   `mac_h == w_tag`. A mismatch instead sets the slot's sticky `FAULT` bit
   and raises `fault_valid` — Appendix F's fail-stop disposition. There is
   no "proceed best-effort" arm, and no arm that installs an entry the tag
   did not cover.
3. **The primitive is a drop-in.** Replacing `xsE`/`macRound` with
   SipHash-2-4 or AES-CMAC changes `w_st = W_MAC`'s round count and nothing
   else — not the dispositions, not the cache, not the check order. The
   assumption this layer asks for is therefore exactly "the keyed
   compression function is unforgeable under the engine-held key", and it
   is confined to one 12-line definition.

Recorded in `CAPWALK_SPEC.md` §Deviations CE4/CE5.

## Memories are BRAM-shaped (D19/D20)

Every bank is read only through dedicated unconditional register latches
with pairwise-distinct address expressions, so `Design.syncReadOkB` holds
for all six banks (`cell_epoch` and `cell_flags` each have three sites —
check unit, walker, drop/mint unit — at three distinct address registers).

## Outcome encoding

`Protocol.Outcome`'s constructor order, plus the fail-stop code:
`ok = 0`, `badref = 1`, `stale = 2`, `denied = 3`, **`fault = 4`**
(deviation CE3 — §2.2's mapping has no code for "the backing store lied",
because Layer 1 has no corruption event; C5).
-/

namespace Machines.CapWalk.Engine

open Loom.Hw

/-! ## Configuration -/

/-- Engine geometry.

* `ew` — epoch width (§2.2's embedded cell is 39 bits; v1 ships 32, as §3's
  engine does — deviation CE1);
* `sw` — the **on-chip** slot-index width: the engine holds `2^sw` embedded
  cells. §2.2's handle carries a 24-bit slot field, so `slot ≥ 2^sw` is
  §2.2's "out-of-range/malformed slot index" and is `-BADREF`
  (Layer-1 C13, in hardware);
* `cw` — hot-cache index width (`2^cw` direct-mapped lines);
* `lw` — lineage-cell index width; must match the epoch engine's `aw` so the
  broadcast wires straight across. -/
structure Cfg where
  /-- Emitted module name. -/
  name : String
  /-- Epoch width. -/
  ew : Nat
  /-- On-chip slot-index width. -/
  sw : Nat
  /-- Hot-cache index width. -/
  cw : Nat
  /-- Lineage-cell index width. -/
  lw : Nat

/-- §2.2's architectural slot-field width, `bits[62:39]`. -/
def SLOTB : Nat := 24

/-! ## Architected constants -/

/-- `Protocol.Outcome.ok`. -/
def OUT_OK : Nat := 0
/-- `Protocol.Outcome.badref`. -/
def OUT_BADREF : Nat := 1
/-- `Protocol.Outcome.stale`. -/
def OUT_STALE : Nat := 2
/-- `Protocol.Outcome.denied`. -/
def OUT_DENIED : Nat := 3
/-- The fail-stop disposition: the fill did not authenticate (deviation CE3). -/
def OUT_FAULT : Nat := 4

/-- `req_op`: §2.2's use-check. -/
def OP_CHECK : Nat := 0
/-- `req_op`: drop the slot (bump the embedded cell, vacate). -/
def OP_DROP : Nat := 1
/-- `req_op`: re-incarnate the slot (bump the embedded cell, occupy). -/
def OP_MINT : Nat := 2

/-- `cell_flags` bit 0: the slot is empty (§2.2's "slot occupied", negated so
that the reset image is all-zero — Epoch E13's lesson). -/
def F_VACANT : Nat := 1
/-- `cell_flags` bit 1: saturated death. -/
def F_DEAD : Nat := 2
/-- `cell_flags` bit 2: **fail-stop** — a fill for this slot failed
authentication. Sticky: nothing in the design ever clears it. -/
def F_FAULT : Nat := 4

/-- Check FSM: idle. -/
def K_IDLE : Nat := 0
/-- Check FSM: the cell/cache read is in the memories' read stage. -/
def K_RD : Nat := 1
/-- Check FSM: the payload is latched; the lineage-replica read (addressed by
the payload's lineage field) is in its read stage. -/
def K_LIN : Nat := 2
/-- Check FSM: everything is latched — answer, or start a fill. -/
def K_EV : Nat := 3
/-- Check FSM: waiting for the walker. -/
def K_WAIT : Nat := 4

/-- Walker: idle. -/
def W_IDLE : Nat := 0
/-- Walker: issue the read of `P0`. -/
def W_A0 : Nat := 1
/-- Walker: await `P0`. -/
def W_D0 : Nat := 2
/-- Walker: issue the read of `P1`. -/
def W_A1 : Nat := 3
/-- Walker: await `P1`. -/
def W_D1 : Nat := 4
/-- Walker: issue the read of `TAG`. -/
def W_A2 : Nat := 5
/-- Walker: await `TAG`. -/
def W_D2 : Nat := 6
/-- Walker: the five MAC rounds. -/
def W_MAC : Nat := 7
/-- Walker: compare, then install **or** fail-stop. -/
def W_CHK : Nat := 8

/-- Drop/mint FSM: idle. -/
def D_IDLE : Nat := 0
/-- Drop/mint FSM: the cell read is in the memory's read stage. -/
def D_RD : Nat := 1
/-- Drop/mint FSM: apply the bump. -/
def D_DO : Nat := 2

/-! ## EDSL helpers -/

/-- Right-fold a list of actions into a `.seq` chain. -/
def actSeq (as : List Act) : Act := as.foldr (fun x acc => .seq x acc) .skip

/-- 1-bit literal. -/
def L1 (n : Nat) : Expr 1 := .lit (BitVec.ofNat 1 n)
/-- 2-bit literal. -/
def L2 (n : Nat) : Expr 2 := .lit (BitVec.ofNat 2 n)
/-- 3-bit literal. -/
def L3 (n : Nat) : Expr 3 := .lit (BitVec.ofNat 3 n)
/-- 4-bit literal. -/
def L4 (n : Nat) : Expr 4 := .lit (BitVec.ofNat 4 n)
/-- 16-bit literal. -/
def L16 (n : Nat) : Expr 16 := .lit (BitVec.ofNat 16 n)
/-- 18-bit literal (the range comparator's headroom width). -/
def L18 (n : Nat) : Expr 18 := .lit (BitVec.ofNat 18 n)
/-- 32-bit literal. -/
def L32 (n : Nat) : Expr 32 := .lit (BitVec.ofNat 32 n)

/-- Bit `i` of a 3-bit flag word. -/
def bit3 (e : Expr 3) (i : Nat) : Expr 1 := .slice e i 1

/-! ## The keyed compression function

One `xorshift32` round with a keyed message injection. See §Authentication
in the module docstring for exactly what is and is not claimed. -/

/-- `xorshift32(h ^ w ^ k)`, as a combinational cone. -/
def xsE (h w k : Expr 32) : Expr 32 :=
  let y0 : Expr 32 := .xor (.xor h w) k
  let y1 : Expr 32 := .xor y0 (.shl y0 (L32 13))
  let y2 : Expr 32 := .xor y1 (.shr y1 (L32 17))
  .xor y2 (.shl y2 (L32 5))

/-- The same function, on values — the model the DDR image is built with. -/
def xsV (h w k : BitVec 32) : BitVec 32 :=
  let y0 := (h ^^^ w) ^^^ k
  let y1 := y0 ^^^ (y0 <<< 13)
  let y2 := y1 ^^^ (y1 >>> 17)
  y2 ^^^ (y2 <<< 5)

/-- The MAC's initialization vector (a bitstream constant). -/
def MAC_IV : Nat := 0x243F6A88

/-- Round key `i` (bitstream constants; five rounds). -/
def macK : Nat → Nat
  | 0 => 0x9E3779B9
  | 1 => 0x85EBCA6B
  | 2 => 0xC2B2AE35
  | 3 => 0x27D4EB2F
  | _ => 0x165667B1

/-- The authenticator, on values: `TAG = mix⁵(IV; P0lo, P0hi, P1, slot, epoch)`. -/
def macOf (p0 : BitVec 64) (p1 : BitVec 32) (slot epoch : Nat) : BitVec 32 :=
  let h0 := xsV (BitVec.ofNat 32 MAC_IV) (p0.extractLsb' 0 32) (BitVec.ofNat 32 (macK 0))
  let h1 := xsV h0 (p0.extractLsb' 32 32) (BitVec.ofNat 32 (macK 1))
  let h2 := xsV h1 p1 (BitVec.ofNat 32 (macK 2))
  let h3 := xsV h2 (BitVec.ofNat 32 slot) (BitVec.ofNat 32 (macK 3))
  xsV h3 (BitVec.ofNat 32 epoch) (BitVec.ofNat 32 (macK 4))

section
variable (cfg : Cfg)

/-- Epoch-width literal. -/
def LE (n : Nat) : Expr cfg.ew := .lit (BitVec.ofNat cfg.ew n)
/-- The saturation value (`Protocol.maxE`). -/
def maxEpoch : Expr cfg.ew := .lit (BitVec.allOnes cfg.ew)

/-! ### The DDR entry layout

Stride 32 bytes per slot; three of the four 64-bit words are used.

| offset | contents |
|--------|----------|
| `+0x00` | `P0` = `rights[7:0] ‖ cls[15:8] ‖ base[31:16] ‖ len[47:32] ‖ lineage[56:48] ‖ sealed[57] ‖ lifetime[58]` |
| `+0x08` | `P1` = the lineage **stamp** epoch (§2.2's "shared lineage/stamp epoch") |
| `+0x10` | `TAG` (low 32 bits) |
| `+0x18` | reserved |

The **embedded** epoch is deliberately absent: it is the on-chip cell
(deviation C1), and its absence from the store is what makes replay a
detectable event rather than a modelling assumption. -/

/-- Byte stride of one backing entry. -/
def ENT_STRIDE : Nat := 32

/-! ### Register / input names -/

def kSt : Expr 3 := .reg 3 "k_st"
def kSlot : Expr SLOTB := .reg SLOTB "k_slot"
def kA : Expr cfg.sw := .reg cfg.sw "k_a"
def kIx : Expr cfg.cw := .reg cfg.cw "k_ix"
def kEp : Expr cfg.ew := .reg cfg.ew "k_ep"

def ceKq : Expr cfg.ew := .reg cfg.ew "ce_kq"
def cfKq : Expr 3 := .reg 3 "cf_kq"
def ctQ : Expr (cfg.sw + 1) := .reg (cfg.sw + 1) "ct_q"
def cp0Q : Expr 64 := .reg 64 "cp0_q"
def cp1Q : Expr cfg.ew := .reg cfg.ew "cp1_q"
def linQ : Expr cfg.ew := .reg cfg.ew "lin_q"

/-! ### The §2.2 check, as one mux cone

`Protocol.outcome`'s ordered spine verbatim, with the fail-stop clause
inserted after the structural clause (deviation CE3). -/

/-- The slot index carried by the handle is outside the engine's on-chip
cell table — §2.2's "out-of-range/malformed slot index". -/
def oobE : Expr 1 :=
  .not (.eq (.slice (kSlot) cfg.sw (SLOTB - cfg.sw))
            (.lit (BitVec.ofNat (SLOTB - cfg.sw) 0)))

/-- Structural failure: the decoder said the handle is malformed, or the slot
index does not exist. -/
def structFailE : Expr 1 := .or (.not (.reg 1 "k_wf")) (oobE cfg)

/-- The direct-mapped tag compare: valid bit set and the stored slot index
equal to the requested one. -/
def hitE : Expr 1 :=
  .and (.slice (ctQ cfg) cfg.sw 1) (.eq (.slice (ctQ cfg) 0 cfg.sw) (kA cfg))

/-- The cached payload's fields. -/
def entRights : Expr 8 := .slice (cp0Q) 0 8
def entCls : Expr 8 := .slice (cp0Q) 8 8
def entBase : Expr 16 := .slice (cp0Q) 16 16
def entLen : Expr 16 := .slice (cp0Q) 32 16
def entLineage : Expr cfg.lw := .slice (cp0Q) 48 cfg.lw

/-- `Protocol.rightsSub q.need ed.rights`. -/
def rightsOkE : Expr 1 :=
  .eq (.and (.reg 8 "k_need") (entRights)) (.reg 8 "k_need")

/-- `ed.cls == q.cls`. -/
def clsOkE : Expr 1 := .eq (entCls) (.reg 8 "k_cls")

/-- `Protocol.rangeIn`, computed with two bits of headroom so `off + len` and
`base + blen` cannot wrap. -/
def rangeOkE : Expr 1 :=
  let b : Expr 18 := .zext (entBase) 18
  let l : Expr 18 := .zext (entLen) 18
  let o : Expr 18 := .zext (.reg 16 "k_off") 18
  let n : Expr 18 := .zext (.reg 16 "k_len") 18
  .and (.not (.ult o b)) (.not (.ult (.add b l) (.add o n)))

/-- §3's verdict on the shared lineage cell: the entry's stamp against this
engine's replica of the epoch engine's cell. -/
def linFailE : Expr 1 := .not (.eq (linQ cfg) (cp1Q cfg))

/-- Steps 1–2 of §2.2 are answerable from on-chip state alone, so a handle
that fails them never causes a DDR transaction. -/
def failFastE : Expr 1 :=
  .or (structFailE cfg)
    (.or (bit3 (cfKq) 2)
      (.or (bit3 (cfKq) 0)
        (.or (.not (.eq (ceKq cfg) (kEp cfg))) (bit3 (cfKq) 1))))

/-- **The check.** `Protocol.outcome` in `Protocol.outcome`'s order, with
`OUT_FAULT` immediately after the structural clause. -/
def codeE : Expr 3 :=
  let epHit : Expr 1 := .eq (ceKq cfg) (kEp cfg)
  -- structural: malformed handle / out-of-range slot index
  .mux (structFailE cfg) (L3 OUT_BADREF) <|
  -- fail-stop: this slot's backing entry did not authenticate (CE3)
  .mux (bit3 (cfKq) 2) (L3 OUT_FAULT) <|
  -- 1. slot occupied (empty + matching embedded epoch is BADREF, not STALE)
  .mux (bit3 (cfKq) 0) (.mux epHit (L3 OUT_BADREF) (L3 OUT_STALE)) <|
  -- 2. handle epoch == slot-cell epoch (saturated death is freshness — C4)
  .mux (.not epHit) (L3 OUT_STALE) <|
  .mux (bit3 (cfKq) 1) (L3 OUT_STALE) <|
  -- 3. lineage-cell epoch current
  .mux (linFailE cfg) (L3 OUT_STALE) <|
  -- 4. required rights present
  .mux (.not (rightsOkE)) (L3 OUT_DENIED) <|
  -- 5. range/class valid
  .mux (.not (clsOkE)) (L3 OUT_BADREF) <|
  .mux (.not (rangeOkE)) (L3 OUT_DENIED) (L3 OUT_OK)

/-- Emit a response and go idle. -/
def respond (code : Expr 3) : Act :=
  actSeq [
    .write 1 "resp_valid" (L1 1),
    .write 3 "resp_code" code,
    .write 1 "k_busy" (L1 0),
    .write 3 "k_st" (L3 K_IDLE) ]

/-- The check unit. Accept → read stage → lineage read stage → evaluate,
answering from on-chip state or handing the slot to the walker. -/
def chkRule : Rule :=
  ⟨"chk",
    actSeq [
      .write 1 "resp_valid" (L1 0),
      .ite (.eq (kSt) (L3 K_IDLE))
        (.ite (.and (.reg 1 "req_valid") (.eq (.reg 2 "req_op") (L2 OP_CHECK)))
          (actSeq [
            .write SLOTB "k_slot" (.reg SLOTB "req_slot"),
            .write cfg.sw "k_a" (.slice (.reg SLOTB "req_slot") 0 cfg.sw),
            .write cfg.cw "k_ix" (.slice (.reg SLOTB "req_slot") 0 cfg.cw),
            .write cfg.ew "k_ep" (.reg cfg.ew "req_epoch"),
            .write 8 "k_need" (.reg 8 "req_need"),
            .write 8 "k_cls" (.reg 8 "req_cls"),
            .write 16 "k_off" (.reg 16 "req_off"),
            .write 16 "k_len" (.reg 16 "req_len"),
            .write 1 "k_wf" (.reg 1 "req_wf"),
            .write 1 "k_busy" (L1 1),
            .write 3 "k_st" (L3 K_RD) ])
          .skip) <|
      .ite (.eq (kSt) (L3 K_RD)) (.write 3 "k_st" (L3 K_LIN)) <|
      .ite (.eq (kSt) (L3 K_LIN)) (.write 3 "k_st" (L3 K_EV)) <|
      .ite (.eq (kSt) (L3 K_EV))
        (.ite (.or (failFastE cfg) (hitE cfg))
          (respond (codeE cfg))
          -- miss on steps 3-5: hand the slot to the walker, unless the
          -- drop/mint unit is mid-bump (CE10 keeps the two commit states
          -- mutually exclusive, so each shared bank has ONE write port)
          (.ite (.eq (.reg 2 "d_st") (L2 D_IDLE))
            (actSeq [
              .write cfg.sw "w_a" (kA cfg),
              .write cfg.cw "w_ix" (kIx cfg),
              .write SLOTB "w_slot" (kSlot),
              .write 16 "fill_cyc" (L16 0),
              .write 4 "w_st" (L4 W_A0),
              .write 3 "k_st" (L3 K_WAIT) ])
            .skip)) <|
      .ite (.eq (kSt) (L3 K_WAIT))
        (.ite (.reg 1 "w_ok")
          -- the line is resident now: re-read and evaluate
          (.write 3 "k_st" (L3 K_RD))
          (.ite (.reg 1 "w_fault") (respond (L3 OUT_FAULT)) .skip))
        .skip ]⟩

/-! ## The walker / fill sequencer -/

/-- The message word absorbed in MAC round `mac_cnt`. -/
def macWordE : Expr 32 :=
  let c : Expr 3 := .reg 3 "mac_cnt"
  .mux (.eq c (L3 0)) (.slice (.reg 64 "w_p0") 0 32) <|
  .mux (.eq c (L3 1)) (.slice (.reg 64 "w_p0") 32 32) <|
  .mux (.eq c (L3 2)) (.zext (.reg cfg.ew "w_p1") 32) <|
  .mux (.eq c (L3 3)) (.zext (.reg SLOTB "w_slot") 32)
    -- round 4 binds the ON-CHIP embedded epoch: this is the replay check
    (.zext (.reg cfg.ew "ce_wq") 32)

/-- The round key for MAC round `mac_cnt`. **D39**: these are engine-owned
*registers* (`keyRegs`), held off the module interface by the design's
`outputs` selection — they were literals while every register published a
port (the retired deviation CE5). -/
def macKeyE : Expr 32 :=
  let c : Expr 3 := .reg 3 "mac_cnt"
  .mux (.eq c (L3 0)) (.reg 32 "mac_k0") <|
  .mux (.eq c (L3 1)) (.reg 32 "mac_k1") <|
  .mux (.eq c (L3 2)) (.reg 32 "mac_k2") <|
  .mux (.eq c (L3 3)) (.reg 32 "mac_k3") (.reg 32 "mac_k4")

/-- The address of word `j` of slot `w_slot`'s backing entry. -/
def entAddrE (j : Nat) : Expr 32 :=
  .add (.reg 32 "tbl_base")
    (.add (.shl (.zext (.reg SLOTB "w_slot") 32) (L32 5)) (L32 (8 * j)))

/-- Issue one single-beat read through the HP-master handshake. -/
def issue (j : Nat) (next : Nat) : Act :=
  actSeq [
    .write 1 "m_start_rd" (L1 1),
    .write 32 "m_addr" (entAddrE j),
    .write 4 "w_st" (L4 next) ]

/-- The tag the engine expects for the entry it just fetched. -/
def tagOkE : Expr 1 := .eq (.reg 32 "mac_h") (.reg 32 "w_tag")

/-- The walker. Three single-beat reads, five MAC rounds, then **either**
install into the cache **or** fail-stop: poison the slot and raise the
fault. There is no third arm. -/
def walkRule : Rule :=
  ⟨"walk",
    actSeq [
      .write 1 "w_ok" (L1 0),
      .write 1 "w_fault" (L1 0),
      .write 1 "fault_valid" (L1 0),
      .write 1 "m_start_rd" (L1 0),
      .ite (.not (.eq (.reg 4 "w_st") (L4 W_IDLE)))
        (.write 16 "fill_cyc" (.add (.reg 16 "fill_cyc") (L16 1))) .skip,
      .ite (.eq (.reg 4 "w_st") (L4 W_A0)) (issue 0 W_D0) <|
      .ite (.eq (.reg 4 "w_st") (L4 W_D0))
        (.ite (.reg 1 "m_done")
          (.seq (.write 64 "w_p0" (.reg 64 "m_rdata")) (.write 4 "w_st" (L4 W_A1)))
          .skip) <|
      .ite (.eq (.reg 4 "w_st") (L4 W_A1)) (issue 1 W_D1) <|
      .ite (.eq (.reg 4 "w_st") (L4 W_D1))
        (.ite (.reg 1 "m_done")
          (.seq (.write cfg.ew "w_p1" (.slice (.reg 64 "m_rdata") 0 cfg.ew))
                (.write 4 "w_st" (L4 W_A2)))
          .skip) <|
      .ite (.eq (.reg 4 "w_st") (L4 W_A2)) (issue 2 W_D2) <|
      .ite (.eq (.reg 4 "w_st") (L4 W_D2))
        (.ite (.reg 1 "m_done")
          (actSeq [
            .write 32 "w_tag" (.slice (.reg 64 "m_rdata") 0 32),
            .write 32 "mac_h" (.reg 32 "mac_iv"),   -- D39: the IV is a register
            .write 3 "mac_cnt" (L3 0),
            .write 4 "w_st" (L4 W_MAC) ])
          .skip) <|
      .ite (.eq (.reg 4 "w_st") (L4 W_MAC))
        (actSeq [
          .write 32 "mac_h" (xsE (.reg 32 "mac_h") (macWordE cfg) (macKeyE)),
          .write 3 "mac_cnt" (.add (.reg 3 "mac_cnt") (L3 1)),
          .ite (.eq (.reg 3 "mac_cnt") (L3 4)) (.write 4 "w_st" (L4 W_CHK)) .skip ]) <|
      .ite (.eq (.reg 4 "w_st") (L4 W_CHK))
        (.ite (tagOkE)
          -- authenticated: install (`c_tag` lands in `ctagWrRule`)
          (actSeq [
            .memWrite cfg.cw 64 "c_p0" 0 (.reg cfg.cw "w_ix") (.reg 64 "w_p0"),
            .memWrite cfg.cw cfg.ew "c_p1" 0 (.reg cfg.cw "w_ix") (.reg cfg.ew "w_p1"),
            .write 1 "w_ok" (L1 1),
            .write 16 "fill_count" (.add (.reg 16 "fill_count") (L16 1)),
            .write 16 "fill_cycles" (.reg 16 "fill_cyc"),
            .write 4 "w_st" (L4 W_IDLE) ])
          -- NOT authenticated: fail-stop (Appendix F). The slot's `FAULT`
          -- bit is set by `flagWrRule`; there is still no arm that installs.
          (actSeq [
            .write 1 "w_fault" (L1 1),
            .write 1 "fault_valid" (L1 1),
            .write SLOTB "fault_slot" (.reg SLOTB "w_slot"),
            .write 16 "fault_count" (.add (.reg 16 "fault_count") (L16 1)),
            .write 16 "fill_cycles" (.reg 16 "fill_cyc"),
            .write 4 "w_st" (L4 W_IDLE) ]))
        .skip ]⟩

/-! ## Drop / re-incarnate

§2.2: "Dropping a slot bumps its embedded cell, so a stale handle to a
recycled slot fails forever." Neither op installs authority: the entry a
re-incarnated slot resolves to still has to authenticate under the **new**
embedded epoch, and the key is not reachable from software (deviation CE6).
Both ops invalidate the slot's cache line, so a re-incarnation can never be
served the previous incarnation's cached payload. -/

/-- §3's saturating increment (`Protocol.satInc`) on the drop/mint unit's
latched cell epoch. -/
def satIncD : Expr cfg.ew :=
  let e : Expr cfg.ew := .reg cfg.ew "ce_dq"
  .mux (.eq e (maxEpoch cfg)) e (.add e (LE cfg 1))

/-- The post-bump flag word: vacancy is set by `drop` and cleared by `mint`,
death is set exactly at saturation, and **`FAULT` is never cleared**. -/
def bumpedFlagsD : Expr 3 :=
  let isDrop : Expr 1 := .eq (.reg 2 "d_op") (L2 OP_DROP)
  .or (.mux isDrop (.or (.reg 3 "cf_dq") (L3 F_VACANT))
                   (.and (.reg 3 "cf_dq") (L3 (F_DEAD + F_FAULT))))
      (.mux (.eq (satIncD cfg) (maxEpoch cfg)) (L3 F_DEAD) (L3 0))

def opRule : Rule :=
  ⟨"op",
    actSeq [
      .write 1 "op_done" (L1 0),
      .ite (.eq (.reg 2 "d_st") (L2 D_IDLE))
        (.ite (.and (.and (.reg 1 "req_valid")
                          (.not (.eq (.reg 2 "req_op") (L2 OP_CHECK))))
                    (.eq (.reg 4 "w_st") (L4 W_IDLE)))
          (actSeq [
            .write cfg.sw "d_a" (.slice (.reg SLOTB "req_slot") 0 cfg.sw),
            .write cfg.cw "d_ix" (.slice (.reg SLOTB "req_slot") 0 cfg.cw),
            .write 2 "d_op" (.reg 2 "req_op"),
            .write 2 "d_st" (L2 D_RD) ])
          .skip) <|
      .ite (.eq (.reg 2 "d_st") (L2 D_RD)) (.write 2 "d_st" (L2 D_DO)) <|
      .ite (.eq (.reg 2 "d_st") (L2 D_DO))
        (actSeq [
          .memWrite cfg.sw cfg.ew "cell_epoch" 0 (.reg cfg.sw "d_a") (satIncD cfg),
          -- `cell_flags` lands in `flagWrRule` and the cache-line
          -- invalidation in `ctagWrRule` (CE10)
          .write 1 "op_done" (L1 1),
          .write 2 "d_st" (L2 D_IDLE) ])
        .skip ]⟩

/-! ## The two shared banks have exactly ONE write port each

`c_tag` is written by the walker (install) and by the drop/mint unit
(invalidate); `cell_flags` by the walker (fail-stop) and by the drop/mint
unit (the bump). Two syntactic write sites means two `Compile` write ports,
and a Xilinx block RAM has **two ports total** — so `cell_flags` (three
read sites + two writes) fell out of block RAM into 1024 flops and a
3069-mux read interface. Measured, then fixed: with this shape plus CE9's
the engine was 9 523 LUTs / 3 982 FFs, and it is now 671 / 442
(deviation CE10, §FIT).

The fix is one muxed write site per bank, plus the interlock in `chkRule`
and `opRule` that keeps `d_st = D_DO` and `w_st = W_CHK` mutually
exclusive — so the mux priority below is a don't-care, not a policy. -/

/-- The single `c_tag` write port: install on an authenticated fill,
invalidate on a drop or a re-incarnation. -/
def ctagWrRule : Rule :=
  let inv : Expr 1 := .eq (.reg 2 "d_st") (L2 D_DO)
  let ins : Expr 1 := .and (.eq (.reg 4 "w_st") (L4 W_CHK)) tagOkE
  ⟨"ctag_wr",
    .ite (.or inv ins)
      (.memWrite cfg.cw (cfg.sw + 1) "c_tag" 0
        (.mux inv (.reg cfg.cw "d_ix") (.reg cfg.cw "w_ix"))
        (.mux inv (.lit (BitVec.ofNat (cfg.sw + 1) 0))
          (.or (.lit (BitVec.ofNat (cfg.sw + 1) (2 ^ cfg.sw)))
               (.zext (.slice (.reg SLOTB "w_slot") 0 cfg.sw) (cfg.sw + 1)))))
      .skip⟩

/-- The single `cell_flags` write port: the fail-stop poison on a failed
authentication, otherwise the drop/mint bump. -/
def flagWrRule : Rule :=
  let flt : Expr 1 := .and (.eq (.reg 4 "w_st") (L4 W_CHK)) (.not tagOkE)
  let bmp : Expr 1 := .eq (.reg 2 "d_st") (L2 D_DO)
  ⟨"flag_wr",
    .ite (.or flt bmp)
      (.memWrite cfg.sw 3 "cell_flags" 0
        (.mux flt (.reg cfg.sw "w_a") (.reg cfg.sw "d_a"))
        (.mux flt (.or (.reg 3 "cf_wq") (L3 F_FAULT)) (bumpedFlagsD cfg)))
      .skip⟩

/-! ## The §3 broadcast sink

`cap_revoke` is a §3 bump on the **epoch engine**; this engine is one more
referent volume of it and adopts the broadcast into its own replica bank.
Software never writes `lin_repl` (deviation CE7). -/

def invalRule : Rule :=
  ⟨"inval",
    .ite (.reg 1 "inval_valid")
      (.memWrite cfg.lw cfg.ew "lin_repl" 0 (.reg cfg.lw "inval_cell")
        (.reg cfg.ew "inval_epoch"))
      .skip⟩

/-! ## Memory read latches (D19 sync-read shape)

Ten unconditional register latches. `cell_epoch` and `cell_flags` each have
three sites at the three distinct address registers `k_a` / `w_a` / `d_a`;
the three cache banks share `k_ix`, which is a *different memory* each time,
so (S3) is per-memory satisfied. `lin_repl`'s address is the cached
payload's lineage field, which is why the check needs the extra `K_LIN`
stage. -/

def latchRules : List Rule :=
  [ ⟨"lat_ce_k", .write cfg.ew "ce_kq" (.memRead cfg.ew "cell_epoch" (kA cfg))⟩,
    ⟨"lat_cf_k", .write 3 "cf_kq" (.memRead 3 "cell_flags" (kA cfg))⟩,
    ⟨"lat_ce_w", .write cfg.ew "ce_wq" (.memRead cfg.ew "cell_epoch" (.reg cfg.sw "w_a"))⟩,
    ⟨"lat_cf_w", .write 3 "cf_wq" (.memRead 3 "cell_flags" (.reg cfg.sw "w_a"))⟩,
    ⟨"lat_ce_d", .write cfg.ew "ce_dq" (.memRead cfg.ew "cell_epoch" (.reg cfg.sw "d_a"))⟩,
    ⟨"lat_cf_d", .write 3 "cf_dq" (.memRead 3 "cell_flags" (.reg cfg.sw "d_a"))⟩,
    ⟨"lat_ct", .write (cfg.sw + 1) "ct_q"
        (.memRead (cfg.sw + 1) "c_tag" (kIx cfg))⟩,
    ⟨"lat_cp0", .write 64 "cp0_q" (.memRead 64 "c_p0" (kIx cfg))⟩,
    ⟨"lat_cp1", .write cfg.ew "cp1_q" (.memRead cfg.ew "c_p1" (kIx cfg))⟩,
    ⟨"lat_lin", .write cfg.ew "lin_q"
        (.memRead cfg.ew "lin_repl" (entLineage cfg))⟩ ]

/-! ## Declarations -/

def chkRegs : List RegDecl :=
  [ ⟨"k_st", 3, 0⟩, ⟨"k_slot", SLOTB, 0⟩, ⟨"k_a", cfg.sw, 0⟩,
    ⟨"k_ix", cfg.cw, 0⟩, ⟨"k_ep", cfg.ew, 0⟩, ⟨"k_need", 8, 0⟩,
    ⟨"k_cls", 8, 0⟩, ⟨"k_off", 16, 0⟩, ⟨"k_len", 16, 0⟩, ⟨"k_wf", 1, 0⟩,
    ⟨"k_busy", 1, 0⟩,
    ⟨"ce_kq", cfg.ew, 0⟩, ⟨"cf_kq", 3, 0⟩, ⟨"ct_q", cfg.sw + 1, 0⟩,
    ⟨"cp0_q", 64, 0⟩, ⟨"cp1_q", cfg.ew, 0⟩, ⟨"lin_q", cfg.ew, 0⟩,
    ⟨"resp_valid", 1, 0⟩, ⟨"resp_code", 3, 0⟩ ]

def walkRegs : List RegDecl :=
  [ ⟨"w_st", 4, 0⟩, ⟨"w_a", cfg.sw, 0⟩, ⟨"w_ix", cfg.cw, 0⟩,
    ⟨"w_slot", SLOTB, 0⟩, ⟨"w_p0", 64, 0⟩, ⟨"w_p1", cfg.ew, 0⟩,
    ⟨"w_tag", 32, 0⟩, ⟨"mac_h", 32, 0⟩, ⟨"mac_cnt", 3, 0⟩,
    ⟨"w_ok", 1, 0⟩, ⟨"w_fault", 1, 0⟩,
    ⟨"ce_wq", cfg.ew, 0⟩, ⟨"cf_wq", 3, 0⟩,
    ⟨"m_start_rd", 1, 0⟩, ⟨"m_addr", 32, 0⟩,
    ⟨"fill_cyc", 16, 0⟩, ⟨"fill_cycles", 16, 0⟩, ⟨"fill_count", 16, 0⟩,
    ⟨"fault_count", 16, 0⟩, ⟨"fault_valid", 1, 0⟩, ⟨"fault_slot", SLOTB, 0⟩ ]

def opRegs : List RegDecl :=
  [ ⟨"d_st", 2, 0⟩, ⟨"d_a", cfg.sw, 0⟩, ⟨"d_ix", cfg.cw, 0⟩, ⟨"d_op", 2, 0⟩,
    ⟨"ce_dq", cfg.ew, 0⟩, ⟨"cf_dq", 3, 0⟩, ⟨"op_done", 1, 0⟩ ]

/-- **The key, as engine-owned state (D39 — this retires deviation CE5).**
The IV and the five round keys are ordinary registers: no rule writes them,
no core-visible path reaches them, and — the part that used to be
impossible — they are **excluded from `Design.outputs`**, so they appear at
no module port. Before D39 every register emitted as an `o_<name>` output,
which is exactly why these six values had to be literals in the mixing cone.

Their reset image is still the compiled-in constant, so this is an
*architectural* secret, not a physical one: the values remain recoverable
from a bitstream readback. What has changed is that the key is now a
*coordinate* — a v2 that loads it from a PUF/TRNG at configuration time is
an added rule, not an EDSL change. -/
def keyRegs : List RegDecl :=
  [ ⟨"mac_iv", 32, BitVec.ofNat 32 MAC_IV⟩,
    ⟨"mac_k0", 32, BitVec.ofNat 32 (macK 0)⟩,
    ⟨"mac_k1", 32, BitVec.ofNat 32 (macK 1)⟩,
    ⟨"mac_k2", 32, BitVec.ofNat 32 (macK 2)⟩,
    ⟨"mac_k3", 32, BitVec.ofNat 32 (macK 3)⟩,
    ⟨"mac_k4", 32, BitVec.ofNat 32 (macK 4)⟩ ]

/-- The request port (D15 inputs). Cores present a **decoded handle** and
what the operation demands, and nothing else: there is no path by which a
core write reaches the cache, a tag, a cell epoch, the fault bits, the
lineage replicas or the MAC key. That is what keeps the eventual safety
statement unconditional over adversarial cores. -/
def reqInputs : List InputDecl :=
  [ ⟨"req_valid", 1⟩, ⟨"req_op", 2⟩, ⟨"req_slot", SLOTB⟩,
    ⟨"req_epoch", cfg.ew⟩, ⟨"req_need", 8⟩, ⟨"req_cls", 8⟩,
    ⟨"req_off", 16⟩, ⟨"req_len", 16⟩, ⟨"req_wf", 1⟩ ]

/-- The DDR side (D15 inputs), the same handshake shape the mini core sees
from `Machines/Lnp64mini/HpMaster` (`m_done` / `m_rdata`), plus the
integration-time table base. Every theorem about this design quantifies
over **all** traces of these ports — that is the point. -/
def memInputs : List InputDecl :=
  [ ⟨"m_done", 1⟩, ⟨"m_rdata", 64⟩, ⟨"tbl_base", 32⟩ ]

/-- The §3 broadcast (D15 inputs), driven by the epoch engine's
`inval_valid`/`inval_cell`/`inval_epoch`. -/
def invalInputs : List InputDecl :=
  [ ⟨"inval_valid", 1⟩, ⟨"inval_cell", cfg.lw⟩, ⟨"inval_epoch", cfg.ew⟩ ]

/-- Cells reset live: epoch 1 (§2.2 reserves epoch 0 as invalid), occupied
(`F_VACANT` clear), unpoisoned, unfaulted; the cache resets empty (`c_tag`
valid bit clear); the lineage replicas reset to epoch 1, in step with the
epoch engine's own reset image.

`cell_flags` and `c_tag` reset **all zero** (Epoch E13's lesson: an
all-zero image is one every configuration path delivers); the only non-zero
images are the two epoch banks, which are exactly the banks the target flow
maps to block RAM. -/
def mems : List MemDecl :=
  [ ⟨"cell_epoch", cfg.sw, cfg.ew, fun _ => 1⟩,
    ⟨"cell_flags", cfg.sw, 3, fun _ => 0⟩,
    ⟨"c_tag", cfg.cw, cfg.sw + 1, fun _ => 0⟩,
    ⟨"c_p0", cfg.cw, 64, fun _ => 0⟩,
    ⟨"c_p1", cfg.cw, cfg.ew, fun _ => 0⟩,
    ⟨"lin_repl", cfg.lw, cfg.ew, fun _ => 1⟩ ]

/-- The open `Design`. Rule order matters twice: `opRule` before `walkRule`
so the shared banks' write-port indices strictly increase along the
syntactic order (`Compile.MemWriteWF`), and the latches first so every read
is the pre-cycle content (D9). -/
def mkDesign : Design where
  name := cfg.name
  regs := chkRegs cfg ++ walkRegs cfg ++ opRegs cfg ++ keyRegs
  -- **D39 (retires CE5).** Everything the engine's users read is exported;
  -- the six key registers are not, so the key sits at no module port. The
  -- exported list is exactly the pre-D39 port list, so `capwalk`'s interface
  -- is unchanged by the key becoming state.
  outputs := (chkRegs cfg ++ walkRegs cfg ++ opRegs cfg).map (·.name)
  mems := mems cfg
  rules := latchRules cfg ++
    [opRule cfg, chkRule cfg, walkRule cfg, ctagWrRule cfg, flagWrRule cfg,
     invalRule cfg]
  inputs := reqInputs cfg ++ memInputs ++ invalInputs cfg

end

/-! ## The shipped instance -/

/-- 32-bit epochs, 1024 on-chip slots, a 256-line hot cache, 512 lineage
cells (matching `Machines.Epoch.Engine.cfg32`'s `aw = 9`).

`cw = 8` is a **fit** decision, recorded as deviation CE9: a 32-line cache
is too shallow for `yosys` to place in block RAM, so it lands in flops and
read muxes (measured: +3.4 k flops and +9 k LUTs). At 256 lines every bank
is block RAM and the engine's LUT cost collapses. -/
def cfg32 : Cfg := { name := "capwalk", ew := 32, sw := 10, cw := 8, lw := 9 }

/-- `capwalk` — the shipped engine. -/
def design : Design := mkDesign cfg32

/-! ## Obligations -/

/-- All six banks are D19 sync-read shaped. -/
def bankNames : List String :=
  ["cell_epoch", "cell_flags", "c_tag", "c_p0", "c_p1", "lin_repl"]

def syncReadOkB (d : Design) : Bool := bankNames.all d.syncReadOkB

def syncReadReport (d : Design) : String :=
  String.intercalate "\n" (bankNames.map d.syncReadReport)

theorem design_syncReadOk : syncReadOkB design = true := by rfl

/-- The write-port discipline is **no longer a local check** (D38): this
engine's `memPortsOkB` — `Compile.MemWriteWF`'s port condition, written by
hand here because `cell_flags` and `c_tag` are the two banks with two
writers — was promoted to Loom as `Design.memPortTraceOkB`, one conjunct of
`Design.realizableOnB`, and `Design.emit` enforces it for every design
against a declared `MemTarget` (`Loom/Hw/MemTarget.lean`). CE10's 14× LUT
finding is what motivated the promotion. What remains here is the
obligation, discharged in the kernel, that this engine meets it. -/
theorem design_memPortTraceOk :
    design.mems.all (fun m => design.memPortTraceOkB m.name) = true := by rfl

set_option maxRecDepth 100000 in
/-- The FastEval side condition, discharged in the kernel, so `fastCycleOpen`
is a *proved* stand-in for `Design.cycleOpen` on this design (D18). -/
theorem design_fastWF : design.fastWFB = true := by rfl

/-- The instantiated open-design theorem: replaying any input trace through
`fastCycleOpen` agrees with the reference semantics on every declared
coordinate — **including** every adversarial `m_done`/`m_rdata` trace. This
is why the attack scenarios below are evidence about the `Design`. -/
theorem fastRunOpen_agrees (n : Nat) (ιs : Nat → InEnv) :
    Agree design
      (fastRunOpen design.elaborate ιs n design.fastReset)
      (design.runOpen ιs n design.reset) :=
  FastEval.fastRunOpen_eq design design_fastWF n ιs _ _
    (FastEval.agree_fastReset design)

/-! ## The backing store, as data

The DDR image the selftest and the iverilog testbench both use. Built here
so the two legs cannot drift: `Emit.lean` writes these words out as
`fpga/zc702/capwalk_ddr.hex`, which the testbench `$readmemh`s. -/

/-- A backing entry, in §2.2's fields. -/
structure Ent where
  /-- §2.2's rights mask. -/
  rights : Nat := 0xFF
  /-- §2.2's object/interface class. -/
  cls : Nat := 1
  /-- Range base. -/
  base : Nat := 0
  /-- Range length. -/
  len : Nat := 0x1000
  /-- The shared lineage cell this entry is on. -/
  lineage : Nat := 0
  /-- §16.3's `SEALED` bit (carried, not acted on — C7). -/
  sealed : Bool := false
  /-- §11.5's lifetime class (carried, not acted on — C7). -/
  lifetime : Nat := 0
  /-- The lineage stamp epoch. -/
  linStamp : Nat := 1
  /-- The **embedded** epoch the tag is bound to. Not stored in DDR: it is
  the on-chip cell, and binding to it is the replay check. -/
  epoch : Nat := 1
  deriving Repr, Inhabited

/-- `P0`, the packed static payload. -/
def Ent.p0 (e : Ent) : BitVec 64 :=
  BitVec.ofNat 64
    (e.rights % 256 + (e.cls % 256) * 2 ^ 8 + (e.base % 65536) * 2 ^ 16 +
      (e.len % 65536) * 2 ^ 32 + (e.lineage % 512) * 2 ^ 48 +
      (if e.sealed then 2 ^ 57 else 0) + (e.lifetime % 2) * 2 ^ 58)

/-- `P1`, the lineage stamp. -/
def Ent.p1 (e : Ent) : BitVec 32 := BitVec.ofNat 32 e.linStamp

/-- The tag the honest store holds for slot `s`. -/
def Ent.tag (e : Ent) (s : Nat) : BitVec 32 := macOf e.p0 e.p1 s e.epoch

/-! ### The demo table

Slots the ladder uses. Slot 261 shares cache index 5 with slot 5
(`cw = 8`), which is what makes the eviction scenario an eviction. -/

def demoTable : Nat → Ent
  | 5 => { rights := 0x0F, cls := 1, base := 0x100, len := 0x40, lineage := 3 }
  | 6 => { rights := 0x03, cls := 1, base := 0x200, len := 0x10, lineage := 4 }
  | 7 => { rights := 0x0F, cls := 1, base := 0x300, len := 0x10, lineage := 4 }
  | 8 => { rights := 0xFF, cls := 1, base := 0x400, len := 0x20, lineage := 4 }
  | 261 => { rights := 0xFF, cls := 1, base := 0x000, len := 0x1000, lineage := 4 }
  | _ => { rights := 0, cls := 0, base := 0, len := 0, lineage := 0 }

/-- How many slots the emitted image covers. -/
def imgSlots : Nat := 512

/-! ### The behavioural DDR, with the three attack modes

Mode `0` is the honest store. The attacks are exactly the three §41
adversaries, and each of them serves a **well-formed** entry — the point is
that well-formedness is not enough. -/

/-- Honest store: `0`. -/
def DDR_OK : Nat := 0
/-- **Attack 1 — corruption.** Slot 6's payload is served with one bit
flipped and the *genuine* tag. -/
def DDR_CORRUPT : Nat := 1
/-- **Attack 2 — substitution.** A read for slot 7 is answered with slot 6's
three words, tag included: a correctly-authenticated entry, for the wrong
slot. -/
def DDR_SUBST : Nat := 2
/-- Honest store, with slot 8 re-issued under embedded epoch 3 — the
positive control for the re-incarnation path. -/
def DDR_REMINT : Nat := 3

/-- The bit the corruption attack flips in slot 6's payload (a rights bit —
i.e. the corruption is an attempted rights amplification). -/
def CORRUPT_BIT : Nat := 4

/-- The behavioural store: `mode → byte address → 64-bit word`. `tbl_base`
is 0 in every harness, so the address is the offset. -/
def ddrWord (mode : Nat) (addr : Nat) : BitVec 64 :=
  let widx := addr / 8
  let slot := widx / 4
  let j := widx % 4
  -- substitution: reads for slot 7 are answered from slot 6
  let src := if mode = DDR_SUBST && slot = 7 then 6 else slot
  let e0 := demoTable src
  -- the re-incarnation control: slot 8's entry re-issued at embedded epoch 3
  let e := if mode = DDR_REMINT && src = 8 then { e0 with epoch := 3 } else e0
  let corrupt := mode = DDR_CORRUPT && src = 6
  match j with
  | 0 => if corrupt then e.p0 ^^^ BitVec.ofNat 64 (2 ^ CORRUPT_BIT) else e.p0
  | 1 => BitVec.setWidth 64 e.p1
  -- the tag is always the GENUINE one: no attack forges a tag, they all
  -- present a correctly-tagged entry in a context the tag does not cover
  | 2 => BitVec.setWidth 64 (e.tag src)
  | _ => 0

/-- The emitted image (mode 0), one 64-bit word per line. -/
def ddrImage : List (BitVec 64) :=
  (List.range (imgSlots * 4)).map (fun w => ddrWord DDR_OK (w * 8))

/-- The re-incarnation image: identical to `ddrImage` except that slot 8's
tag is the one a correct installer would write *after* the embedded cell was
bumped to epoch 3. Emitted as a second hex so the RTL testbench never has to
recompute a MAC. -/
def ddrImageRemint : List (BitVec 64) :=
  (List.range (imgSlots * 4)).map (fun w => ddrWord DDR_REMINT (w * 8))

/-! ## The selftest (D18: the verified fast evaluator *is* the oracle)

There is no hand-written ISS: `fastRunOpen_agrees` makes `fastCycleOpen` a
proved stand-in for `Design.cycleOpen`, so every scenario below is a
statement about the `Design`. The DDR is driven **closed-loop** — the
harness watches `m_start_rd`/`m_addr` and answers `lat` cycles later — so
the walker's handshake is exercised, not stubbed. -/

/-- One cycle of stimulus. `ddr` selects which store the environment is (the
harness's "tell the DDR to lie" knob), and it is *not* a design input. -/
structure Stim where
  /-- Assert the request port. -/
  valid : Bool := false
  /-- `OP_CHECK` / `OP_DROP` / `OP_MINT`. -/
  op : Nat := 0
  /-- The handle's 24-bit slot field. -/
  slot : Nat := 0
  /-- The handle's epoch field. -/
  epoch : Nat := 1
  /-- Rights the operation requires. -/
  need : Nat := 0x0F
  /-- Class the operation requires. -/
  cls : Nat := 1
  /-- Requested range offset. -/
  off : Nat := 0x100
  /-- Requested range length. -/
  len : Nat := 1
  /-- The decoder's structural verdict. -/
  wf : Bool := true
  /-- Drive the §3 broadcast this cycle. -/
  inv : Bool := false
  /-- Broadcast cell. -/
  invCell : Nat := 0
  /-- Broadcast epoch. -/
  invEpoch : Nat := 0
  /-- Which behavioural store answers this cycle. -/
  ddr : Nat := 0
  deriving Repr

def idle : Stim := {}

/-- The design inputs driven by one `Stim`, plus the DDR response the
harness computes. -/
def stimEnv (s : Stim) (mdone : Bool) (mrdata : BitVec 64) : InEnv := fun n w =>
  if n = "req_valid" then (BitVec.ofBool s.valid).setWidth w
  else if n = "req_op" then (BitVec.ofNat 2 s.op).setWidth w
  else if n = "req_slot" then (BitVec.ofNat SLOTB s.slot).setWidth w
  else if n = "req_epoch" then (BitVec.ofNat 64 s.epoch).setWidth w
  else if n = "req_need" then (BitVec.ofNat 8 s.need).setWidth w
  else if n = "req_cls" then (BitVec.ofNat 8 s.cls).setWidth w
  else if n = "req_off" then (BitVec.ofNat 16 s.off).setWidth w
  else if n = "req_len" then (BitVec.ofNat 16 s.len).setWidth w
  else if n = "req_wf" then (BitVec.ofBool s.wf).setWidth w
  else if n = "m_done" then (BitVec.ofBool mdone).setWidth w
  else if n = "m_rdata" then mrdata.setWidth w
  else if n = "tbl_base" then 0#w
  else if n = "inval_valid" then (BitVec.ofBool s.inv).setWidth w
  else if n = "inval_cell" then (BitVec.ofNat 32 s.invCell).setWidth w
  else if n = "inval_epoch" then (BitVec.ofNat 64 s.invEpoch).setWidth w
  else 0#w

/-- What the ladder watches each cycle. -/
structure Obs where
  /-- Cycle index. -/
  k : Nat
  /-- Response pulse. -/
  rv : Nat
  /-- Outcome code. -/
  rc : Nat
  /-- Fail-stop pulse. -/
  fv : Nat
  /-- The slot the fail-stop names. -/
  fs : Nat
  /-- Fills that authenticated, cumulative. -/
  fills : Nat
  /-- Fills that did not, cumulative. -/
  faults : Nat
  /-- Latched fill latency (issue → install-or-fault). -/
  fcyc : Nat
  deriving Repr

def peekN (d : Design) (fs : FastSt) (n : String) : Nat :=
  ((d.fastRegs fs).lookup n).getD 0

/-- Run a stimulus list through the verified fast evaluator with a
closed-loop behavioural DDR of latency `lat`, recording the observation
after every cycle. -/
def runSim (d : Design) (lat : Nat) (ss : List Stim) : List Obs := Id.run do
  let fd := d.elaborate
  let mut fs := d.fastReset
  let mut out : List Obs := []
  let mut k := 0
  -- `pend = some (countdown, address)` — the in-flight DDR read
  let mut pend : Option (Nat × Nat) := none
  for s in ss do
    let mut mdone := false
    let mut mrdata : BitVec 64 := 0
    match pend with
    | some (0, a) => mdone := true; mrdata := ddrWord s.ddr a; pend := none
    | some (n + 1, a) => pend := some (n, a)
    | none => pure ()
    fs := fastCycleOpen fd (stimEnv s mdone mrdata) fs
    if peekN d fs "m_start_rd" = 1 then
      pend := some (lat, peekN d fs "m_addr")
    out := out ++ [{ k := k
                     rv := peekN d fs "resp_valid", rc := peekN d fs "resp_code"
                     fv := peekN d fs "fault_valid", fs := peekN d fs "fault_slot"
                     fills := peekN d fs "fill_count"
                     faults := peekN d fs "fault_count"
                     fcyc := peekN d fs "fill_cycles" }]
    k := k + 1
  return out

/-- The outcome codes reported, in order. -/
def codes (obs : List Obs) : List Nat :=
  (obs.filter (fun o => o.rv = 1)).map (·.rc)

/-- The final `(fills, faults)` counters. -/
def counters (obs : List Obs) : List Nat :=
  match obs.reverse with
  | [] => [0, 0]
  | o :: _ => [o.fills, o.faults]

/-! ### Stimulus builders -/

def gap (n : Nat) : List Stim := List.replicate n idle

/-- A check plus enough idle cycles for a **hit** to answer. -/
def chk (slot ep : Nat) (need : Nat := 0x0F) (cls : Nat := 1)
    (off : Nat := 0x100) (len : Nat := 1) (wf : Bool := true)
    (ddr : Nat := 0) : List Stim :=
  { valid := true, op := OP_CHECK, slot := slot, epoch := ep, need := need,
    cls := cls, off := off, len := len, wf := wf, ddr := ddr }
  :: (gap 8).map (fun s => { s with ddr := ddr })

/-- A check plus enough idle cycles for a **miss, fill and re-evaluation**. -/
def chkM (slot ep : Nat) (need : Nat := 0x0F) (cls : Nat := 1)
    (off : Nat := 0x100) (len : Nat := 1) (wf : Bool := true)
    (ddr : Nat := 0) : List Stim :=
  { valid := true, op := OP_CHECK, slot := slot, epoch := ep, need := need,
    cls := cls, off := off, len := len, wf := wf, ddr := ddr }
  :: (gap 39).map (fun s => { s with ddr := ddr })

/-- A drop or a re-incarnation, plus the cycles it needs. -/
def opSeq (op slot : Nat) (ddr : Nat := 0) : List Stim :=
  { valid := true, op := op, slot := slot, ddr := ddr }
  :: (gap 5).map (fun s => { s with ddr := ddr })

/-- One §3 broadcast cycle (the epoch engine bumping lineage cell `c` to
epoch `e`), plus settling. -/
def invSeq (c e : Nat) : List Stim :=
  { inv := true, invCell := c, invEpoch := e } :: gap 3

private def expect (name : String) (got want : List Nat) : IO Nat := do
  if got = want then
    IO.println s!"  OK   {name}: {got}"
    return 0
  else
    IO.println s!"  FAIL {name}: got {got} want {want}"
    return 1

/-- The engine acceptance ladder. Each scenario is named for the §2.2
sentence, the Layer-1 theorem, or the §41 adversary it exercises. -/
def selftest : IO Unit := do
  let mut bad := 0
  -- (1) cold start: every slot misses, so the first check is miss → fill → hit.
  bad := bad + (← expect "miss→fill→ok        " (codes (runSim design 2 (chkM 5 1))) [OUT_OK])
  bad := bad + (← expect "  …one fill, no fault"
    (counters (runSim design 2 (chkM 5 1))) [1, 0])
  -- (2) hit: the second check answers from the cache with NO fabric transaction.
  let t2 := runSim design 2 (chkM 5 1 ++ chk 5 1)
  bad := bad + (← expect "hit (no second fill)" (codes t2) [OUT_OK, OUT_OK])
  bad := bad + (← expect "  …fill_count still 1" (counters t2) [1, 0])
  -- (3) eviction: slot 261 shares cache index 5, so it displaces slot 5 and
  -- slot 5's next use must re-fill.
  let t3 := runSim design 2 (chkM 5 1 ++ chkM 261 1 (need := 0xFF) (off := 0)
                              ++ chkM 5 1)
  bad := bad + (← expect "evict → refill      " (codes t3) [OUT_OK, OUT_OK, OUT_OK])
  bad := bad + (← expect "  …three fills      " (counters t3) [3, 0])
  -- (4) -DENIED: a live, current, in-class reference lacking rights (§2.2's
  -- step 4, strictly after freshness).
  bad := bad + (← expect "rights → -DENIED    "
    (codes (runSim design 2 (chkM 5 1 (need := 0xF0)))) [OUT_DENIED])
  -- (4b) -BADREF: wrong object/interface class, and an out-of-range slot.
  bad := bad + (← expect "class → -BADREF     "
    (codes (runSim design 2 (chkM 5 1 (cls := 2)))) [OUT_BADREF])
  bad := bad + (← expect "slot ≥ 2^sw → -BADREF"
    (codes (runSim design 2 (chk 0x100005 1))) [OUT_BADREF])
  -- (4c) -STALE on the embedded cell: answered on-chip, so it never reaches DDR.
  bad := bad + (← expect "embedded ep → -STALE"
    (counters (runSim design 2 (chk 5 9))) [0, 0])
  -- (5) -STALE after a lineage bump: one §3 bump on the shared cell, and the
  -- SAME cached entry now fails (Layer-1 T-C4, discharged by §3's T-E1).
  let t5 := runSim design 2 (chkM 5 1 ++ invSeq 3 2 ++ chk 5 1)
  bad := bad + (← expect "lineage bump → -STALE" (codes t5) [OUT_OK, OUT_STALE])
  -- ===================== the three fill attacks =====================
  -- (A1) CORRUPTION: slot 6's payload arrives with a rights bit flipped and
  -- its genuine tag. Detected; the slot is poisoned, fail-stop.
  let a1 := runSim design 2 (chkM 6 1 (need := 0x03) (off := 0x200)
                              (ddr := DDR_CORRUPT))
  bad := bad + (← expect "A1 corrupted  → FAULT" (codes a1) [OUT_FAULT])
  bad := bad + (← expect "  …0 fills, 1 fault " (counters a1) [0, 1])
  bad := bad + (← expect "  …fault names slot 6"
    ((a1.filter (fun o => o.fv = 1)).map (·.fs)) [6])
  -- and the poison is permanent: an honest store afterwards does not revive it
  let a1b := runSim design 2 (chkM 6 1 (need := 0x03) (off := 0x200)
                                (ddr := DDR_CORRUPT)
                              ++ chkM 6 1 (need := 0x03) (off := 0x200))
  bad := bad + (← expect "  …poison permanent " (codes a1b) [OUT_FAULT, OUT_FAULT])
  -- (A2) SUBSTITUTION: slot 7 is answered with slot 6's entry — correctly
  -- tagged, wrong slot. The tag binds the slot, so it is detected.
  let a2 := runSim design 2 (chkM 7 1 (off := 0x300) (ddr := DDR_SUBST))
  bad := bad + (← expect "A2 substituted→ FAULT" (codes a2) [OUT_FAULT])
  bad := bad + (← expect "  …fault names slot 7"
    ((a2.filter (fun o => o.fv = 1)).map (·.fs)) [7])
  -- (A2 control) the very same words, served for slot 6, DO authenticate.
  bad := bad + (← expect "  …control: slot 6 ok"
    (codes (runSim design 2 (chkM 6 1 (need := 0x03) (off := 0x200)))) [OUT_OK])
  -- (A3) REPLAY: drop and re-incarnate slot 5 (embedded epoch 1 → 3), then
  -- serve the honest, correctly-tagged, previous-incarnation entry.
  let replay := opSeq OP_DROP 5 ++ opSeq OP_MINT 5 ++ chkM 5 3
  let a3 := runSim design 2 replay
  bad := bad + (← expect "A3 replayed   → FAULT" (codes a3) [OUT_FAULT])
  bad := bad + (← expect "  …0 fills, 1 fault " (counters a3) [0, 1])
  -- (A3 control) the same drop/re-incarnate on slot 8, against a store that
  -- re-issued slot 8's entry under the NEW embedded epoch: authenticates.
  let a3c := runSim design 2 (opSeq OP_DROP 8 (ddr := DDR_REMINT)
                              ++ opSeq OP_MINT 8 (ddr := DDR_REMINT)
                              ++ chkM 8 3 (need := 0xFF) (off := 0x400)
                                   (ddr := DDR_REMINT))
  bad := bad + (← expect "  …control: re-issued" (codes a3c) [OUT_OK])
  bad := bad + (← expect "  …one fill, 0 faults" (counters a3c) [1, 0])
  -- (6) reuse safety (Layer-1 T-C5): the pre-drop handle never validates again.
  bad := bad + (← expect "pre-drop handle     "
    (codes (runSim design 2 (opSeq OP_DROP 5 ++ opSeq OP_MINT 5 ++ chk 5 1)))
    [OUT_STALE])
  if bad = 0 then
    IO.println "CAPWALK ENGINE SELFTEST OK — hit/miss/fill/evict, §2.2 precedence, lineage -STALE, and all three fill attacks detected"
  else
    IO.println s!"CAPWALK ENGINE SELFTEST FAILED ({bad})"

/-- Report the measured fill latency, which is the engine's headline number. -/
def latency : IO Unit := do
  let t := runSim design 2 (chkM 5 1)
  let f := (t.filter (fun o => o.rv = 1)).map (·.fcyc)
  IO.println s!"fill latency (miss→3 DDR beats→MAC→install): {f} cycles (DDR latency 2)"

/-- `fastCycleOpen` ≡ the reference `Design.cycleOpen` on the acceptance
stimulus — the D18 corroboration leg beside the proof. Replays the same
closed-loop DDR against `Design.cycleOpen` directly. -/
def refCheck : IO Unit := do
  let ss := chkM 5 1 ++ chk 5 1 ++ chkM 6 1 (need := 0x03) (off := 0x200)
              (ddr := DDR_CORRUPT)
  -- resolve the DDR responses by first running the fast evaluator, then
  -- replaying the resulting input trace against both semantics
  let fd := design.elaborate
  let mut fs := design.fastReset
  let mut envs : List InEnv := []
  let mut pend : Option (Nat × Nat) := none
  for s in ss do
    let mut mdone := false
    let mut mrdata : BitVec 64 := 0
    match pend with
    | some (0, a) => mdone := true; mrdata := ddrWord s.ddr a; pend := none
    | some (n + 1, a) => pend := some (n, a)
    | none => pure ()
    let e := stimEnv s mdone mrdata
    envs := envs ++ [e]
    fs := fastCycleOpen fd e fs
    if peekN design fs "m_start_rd" = 1 then
      pend := some (2, peekN design fs "m_addr")
  let ok ← design.lockstep envs.length (fun c => (envs.getD c (stimEnv idle false 0)))
  if ok then IO.println "CAPWALK ENGINE REF LOCKSTEP OK (fastCycleOpen ≡ Design.cycleOpen)"
  else IO.println "CAPWALK ENGINE REF LOCKSTEP FAILED"

/-! ### The iverilog testbench's stimulus, as one continuous run

`fpga/zc702/tb_capwalk.v` replays *exactly* this trace against
`rtl/capwalk.v` and a behavioural DDR loaded from
`fpga/zc702/capwalk_ddr.hex`, and prints the same event lines, which makes
the RTL leg a literal `diff` against the verified fast evaluator.

Memories are not reset by `rst`, so the scenarios are chained on distinct
slots rather than restarted — the same discipline `tb_epochengine.v` uses. -/

def tbTrace : List Stim :=
  chkM 5 1                                    -- (a) miss → fill      → ok
  ++ chk 5 1                                  -- (b) hit              → ok
  ++ chkM 261 1 (need := 0xFF) (off := 0)      -- (c) evicts index 5   → ok
  ++ chkM 5 1                                 -- (d) refill           → ok
  ++ chk 5 1 (need := 0xF0)                   -- (e) rights           → -DENIED
  ++ chk 5 1 (cls := 2)                       -- (f) class            → -BADREF
  ++ chk 0x100005 1                           -- (g) slot ≥ 2^sw      → -BADREF
  ++ chk 5 9                                  -- (h) embedded epoch   → -STALE
  ++ invSeq 3 2 ++ chk 5 1                    -- (i) lineage bump     → -STALE
  ++ chkM 6 1 (need := 0x03) (off := 0x200) (ddr := DDR_CORRUPT)
                                              -- (A1) corrupted       → FAULT
  ++ chkM 6 1 (need := 0x03) (off := 0x200)   -- (A1b) poison permanent
  ++ chkM 7 1 (off := 0x300) (ddr := DDR_SUBST)
                                              -- (A2) substituted     → FAULT
  ++ opSeq OP_DROP 8 (ddr := DDR_REMINT)
  ++ opSeq OP_MINT 8 (ddr := DDR_REMINT)
  ++ chkM 8 3 (need := 0xFF) (off := 0x400) (ddr := DDR_REMINT)
                                              -- (ctl) re-issued      → ok
  ++ opSeq OP_DROP 5 ++ opSeq OP_MINT 5
  ++ chkM 5 3                                 -- (A3) replayed        → FAULT

/-- Emit the ladder's expected observations, so the iverilog testbench checks
the *same* oracle the Lean selftest does. -/
def predict : IO Unit := do
  IO.println "--- capwalk ---"
  for o in runSim design 2 tbTrace do
    if o.rv = 1 || o.fv = 1 then
      IO.println s!"{o.k} rv={o.rv} rc={o.rc} fv={o.fv} fs={o.fs} fills={o.fills} faults={o.faults}"

end Machines.CapWalk.Engine

