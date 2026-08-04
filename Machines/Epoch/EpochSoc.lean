-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Epoch.Engine
import Machines.Lnp64mini.DualSoc
import Loom.Hw.Compose

/-!
# `lnp64mini_epoch` — the dual core with the epoch engine on the GP aperture

`EPOCH_SPEC.md` §"Core integration + demo": the two ops enter through the
existing GP MMIO aperture (`l_is_gp`/`s_is_gp`), **not** as new opcodes, so
the core's proved ladder is untouched. This file adds two designs and
composes; `Machines/Lnp64mini/{Soc,DualSoc}.lean` are not edited, so
`lnp64mini_soc.v` and `lnp64mini_dual.v` stay byte-identical.

```
lnp64mini_epoch = c0 ∥ c1 ∥ arb ∥ hp ∥ gpm ∥ ep ∥ mm0 ∥ mm1
```

## The seam

`Machines.Lnp64mini.Core`'s GP aperture already decodes
`ea[31:20] == 0x0A0` (the mini3 wrapper's "DDR scratch window routed
through the GP"). One 4 KiB page of it, **`0x0A0E_0000`**, is carved out
for the engine: a store there no longer starts the AXI GP master
(`gpm_start_*` is gated with `¬ep_sel`), and the core's `gp_done`/
`gp_rdata` are muxed from the per-core `epochmmio` block instead.

Word map (byte offsets from `0x0A0E_0000`, 32-bit accesses — `LD.W`/`ST.W`):

| off | write | read |
|-----|-------|------|
| 0x00 | cell index | cell index |
| 0x04 | presented epoch (§3's `ref.epoch`) | presented epoch |
| 0x08 | `{rights, classOk, wellFormed}` (resets to 7) | same |
| 0x0C | **fire CHECK** | `{chk_pend, chk_busy}` |
| 0x10 | — | **RESULT** `{valid<<8, Outcome code}` — *blocks* until the check answers |
| 0x14 | **fire BUMP** (bit 0 = poison policy) | `{bmp_pend, bump_busy}` |
| 0x18 | — | **bump latency** — *blocks* until the bump returns (§3's return point) |
| 0x1C | — | ID `0xE90C0001` |

## Why both cores use the *same* address

`EPOCH_SPEC.md` asks for "distinct addresses"; what is distinct is the
*word* (check / bump / status / latency), not the per-core base. A core's
referent volume is **wired, not addressed**: core `k` reaches request port
`k` and check unit `k` reads replica bank `k`, and there is no address a
core can name that reaches the other volume's bank. If the volume were
selected by address, an adversarial core could ask for a check against the
other volume's replica — precisely the class of thing the superseding
doctrine exists to make impossible. Recorded as deviation E6.
-/

namespace Machines.Epoch.EpochSoc

-- `actSeq` also lives in `Loom.Hw` (Trees.lean), which lnp64mini now imports
-- transitively; hide it here so the Engine's stays unambiguous.
open Loom.Hw hiding actSeq
open Machines.Epoch.Engine (Cfg cfg32 actSeq L1 L2 L3 L16)

/-! ## `epochmmio` — the per-core GP-transaction adapter

A tiny MMIO slave: it stages §3's `Req` fields, fires one request pulse at
the engine, and holds the core's GP transaction open (`done` low) until the
engine answers. It owns **no** freshness state — `cell`/`epoch`/`flags`
are the handle the *core already holds*, which is exactly `Protocol.Req`. -/

namespace Mmio

variable (cfg : Cfg)

def gpRd : Expr 1 := .reg 1 "gp_rd"
def gpWr : Expr 1 := .reg 1 "gp_wr"
def gpAddr : Expr 32 := .reg 32 "gp_addr"
def gpWdata : Expr 32 := .reg 32 "gp_wdata"
def sel : Expr 1 := .reg 1 "sel"
def respValid : Expr 1 := .reg 1 "resp_valid"
def respCode : Expr 3 := .reg 3 "resp_code"
def chkBusy : Expr 1 := .reg 1 "chk_busy"
def bumpBusy : Expr 1 := .reg 1 "bump_busy"
def bumpDone : Expr 1 := .reg 1 "bump_done"
def bumpCycles : Expr 16 := .reg 16 "bump_cycles"

def qActive : Expr 1 := .reg 1 "q_active"
def qIdx : Expr 3 := .reg 3 "q_idx"
def chkPend : Expr 1 := .reg 1 "chk_pend"
def bmpPend : Expr 1 := .reg 1 "bmp_pend"
def resV : Expr 1 := .reg 1 "res_v"
def resCode : Expr 3 := .reg 3 "res_code"
def cycR : Expr 16 := .reg 16 "cyc"

/-- The transaction's word index, `addr[4:2]`. -/
def idxE : Expr 3 := .slice gpAddr 2 3
def idxIs (n : Nat) : Expr 3 → Expr 1 := fun e => .eq e (L3 n)

/-- The read mux (32-bit GP reads are `LD.W`, zero-extending). -/
def readMux : Expr 32 :=
  .mux (idxIs 0 qIdx) (.zext (.reg cfg.aw "cell") 32) <|
  .mux (idxIs 1 qIdx) (.zext (.reg cfg.ew "epoch") 32) <|
  .mux (idxIs 2 qIdx) (.zext (.reg 3 "flags") 32) <|
  .mux (idxIs 3 qIdx)
    (.or (.shl (.zext chkPend 32) (.lit 1)) (.zext chkBusy 32)) <|
  .mux (idxIs 4 qIdx)
    (.or (.shl (.zext resV 32) (.lit 8)) (.zext resCode 32)) <|
  .mux (idxIs 5 qIdx)
    (.or (.shl (.zext bmpPend 32) (.lit 1)) (.zext bumpBusy 32)) <|
  .mux (idxIs 6 qIdx) (.zext cycR 32) (.lit 0xE90C0001)

/-- A pending RESULT read blocks until the check unit has answered; a
pending latency read blocks until the bump has returned — §3's
linearization point, exposed as a load that completes exactly then. -/
def stallE : Expr 1 :=
  .or (.and (idxIs 4 qIdx) (.or (.or chkPend chkBusy) respValid))
      (.and (idxIs 6 qIdx) (.or (.or bmpPend bumpBusy) bumpDone))

def body : Act :=
  actSeq [
    .write 1 "done" (L1 0),
    .write 1 "req_valid" (L1 0),
    -- engine responses land here; the core never writes them
    .ite respValid
      (actSeq [ .write 3 "res_code" respCode, .write 1 "res_v" (L1 1),
                .write 1 "chk_pend" (L1 0) ]) .skip,
    .ite bumpDone
      (actSeq [ .write 16 "cyc" bumpCycles, .write 1 "bmp_pend" (L1 0) ]) .skip,
    -- accept one GP transaction
    .ite (.and (.and (.or gpRd gpWr) sel) (.not qActive))
      (actSeq [
        .write 3 "q_idx" idxE,
        .write 1 "q_active" (L1 1),
        .ite gpWr
          (.ite (idxIs 0 idxE) (.write cfg.aw "cell" (.slice gpWdata 0 cfg.aw)) <|
           .ite (idxIs 1 idxE) (.write cfg.ew "epoch" (.slice gpWdata 0 cfg.ew)) <|
           .ite (idxIs 2 idxE) (.write 3 "flags" (.slice gpWdata 0 3)) <|
           .ite (idxIs 3 idxE)
             (actSeq [ .write 1 "req_valid" (L1 1), .write 1 "req_op" (L1 0),
                       .write 1 "chk_pend" (L1 1) ]) <|
           .ite (idxIs 5 idxE)
             (actSeq [ .write 1 "req_valid" (L1 1), .write 1 "req_op" (L1 1),
                       .write 1 "req_policy" (.slice gpWdata 0 1),
                       .write 1 "bmp_pend" (L1 1) ])
             .skip)
          .skip ])
      .skip,
    -- complete it when the engine is ready
    .ite (.and qActive (.not stallE))
      (actSeq [
        .write 1 "done" (L1 1),
        .write 32 "rdata" (readMux cfg),
        .write 1 "q_active" (L1 0),
        .ite (idxIs 4 qIdx) (.write 1 "res_v" (L1 0)) .skip ])
      .skip ]

def design : Design where
  name := "epochmmio"
  regs :=
    [ ⟨"cell", cfg.aw, 0⟩, ⟨"epoch", cfg.ew, 1⟩, ⟨"flags", 3, 7⟩,
      ⟨"req_valid", 1, 0⟩, ⟨"req_op", 1, 0⟩, ⟨"req_policy", 1, 0⟩,
      ⟨"rdata", 32, 0⟩, ⟨"done", 1, 0⟩,
      ⟨"res_code", 3, 0⟩, ⟨"res_v", 1, 0⟩,
      ⟨"chk_pend", 1, 0⟩, ⟨"bmp_pend", 1, 0⟩, ⟨"cyc", 16, 0⟩,
      ⟨"q_active", 1, 0⟩, ⟨"q_idx", 3, 0⟩ ]
  mems := []
  -- D39a: outputs are mandatory and explicit, like inputs.
  outputs :=
    [ "cell", "epoch", "flags", "req_valid", "req_op", "req_policy",
      "rdata", "done", "res_code", "res_v", "chk_pend", "bmp_pend", "cyc",
      "q_active", "q_idx" ]
  rules := [⟨"mmio", body cfg⟩]
  inputs :=
    [ ⟨"gp_rd", 1⟩, ⟨"gp_wr", 1⟩, ⟨"gp_addr", 32⟩, ⟨"gp_wdata", 32⟩,
      ⟨"sel", 1⟩, ⟨"resp_valid", 1⟩, ⟨"resp_code", 3⟩, ⟨"chk_busy", 1⟩,
      ⟨"bump_busy", 1⟩, ⟨"bump_done", 1⟩, ⟨"bump_cycles", 16⟩ ]

end Mmio

/-! ## Instances -/

open Machines.Lnp64mini.DualSoc (c0 c1 arb hp gp owns0)

/-- The engine, prefixed `ep_`. -/
def ep : Design := Machines.Epoch.Engine.design.prefixed "ep_"
/-- Core 0's MMIO adapter. -/
def mm0 : Design := (Mmio.design cfg32).prefixed "mm0_"
/-- Core 1's MMIO adapter. -/
def mm1 : Design := (Mmio.design cfg32).prefixed "mm1_"

/-- The engine page: `gp_addr[31:12] == 0x0A0E0`. -/
def EP_PAGE : Nat := 0x0A0E0

/-- Aperture decode over core `k`'s latched GP address. -/
def epSel (k : Nat) : Expr 1 :=
  .eq (.slice (.reg 32 s!"c{k}_gp_addr_r") 12 20) (.lit (BitVec.ofNat 20 EP_PAGE))

/-! ## Wiring

Everything `Machines.Lnp64mini.DualSoc.wire` does, plus the engine seam.
The five GP entries that change are listed *before* the delegation, so the
rest is literally the dual's wiring. -/

def wire (n : String) (w : Nat) : Option (Expr w) :=
  match n, w with
  -- ---- core GP responses: the engine page, else the AXI GP master ----
  | "c0_gp_done",  1  => some (.mux (epSel 0) (.reg 1  "mm0_done")  (.reg 1  "gpm_done"))
  | "c0_gp_rdata", 32 => some (.mux (epSel 0) (.reg 32 "mm0_rdata") (.reg 32 "gpm_rdata"))
  | "c1_gp_done",  1  => some (.mux (epSel 1) (.reg 1  "mm1_done")  (.lit 1))
  | "c1_gp_rdata", 32 => some (.mux (epSel 1) (.reg 32 "mm1_rdata") (.lit 0))
  -- the AXI GP master must not see an engine-page transaction
  | "gpm_start_wr", 1 => some (.and (.reg 1 "c0_gp_wr") (.not (epSel 0)))
  | "gpm_start_rd", 1 => some (.and (.reg 1 "c0_gp_rd") (.not (epSel 0)))
  -- ---- MMIO adapters ← the cores' GP request registers ----
  | "mm0_gp_rd",    1  => some (.reg 1  "c0_gp_rd")
  | "mm0_gp_wr",    1  => some (.reg 1  "c0_gp_wr")
  | "mm0_gp_addr",  32 => some (.reg 32 "c0_gp_addr_r")
  | "mm0_gp_wdata", 32 => some (.reg 32 "c0_gp_wdata_r")
  | "mm0_sel",      1  => some (epSel 0)
  | "mm1_gp_rd",    1  => some (.reg 1  "c1_gp_rd")
  | "mm1_gp_wr",    1  => some (.reg 1  "c1_gp_wr")
  | "mm1_gp_addr",  32 => some (.reg 32 "c1_gp_addr_r")
  | "mm1_gp_wdata", 32 => some (.reg 32 "c1_gp_wdata_r")
  | "mm1_sel",      1  => some (epSel 1)
  -- ---- MMIO adapters ← engine status/response ----
  | "mm0_resp_valid",  1  => some (.reg 1  "ep_resp0_valid")
  | "mm0_resp_code",   3  => some (.reg 3  "ep_resp0_code")
  | "mm0_chk_busy",    1  => some (.reg 1  "ep_c0_busy")
  | "mm0_bump_busy",   1  => some (.reg 1  "ep_bump_busy")
  | "mm0_bump_done",   1  => some (.reg 1  "ep_bump_done0")
  | "mm0_bump_cycles", 16 => some (.reg 16 "ep_bump_cycles")
  | "mm1_resp_valid",  1  => some (.reg 1  "ep_resp1_valid")
  | "mm1_resp_code",   3  => some (.reg 3  "ep_resp1_code")
  | "mm1_chk_busy",    1  => some (.reg 1  "ep_c1_busy")
  | "mm1_bump_busy",   1  => some (.reg 1  "ep_bump_busy")
  | "mm1_bump_done",   1  => some (.reg 1  "ep_bump_done1")
  | "mm1_bump_cycles", 16 => some (.reg 16 "ep_bump_cycles")
  -- ---- engine request ports ← the MMIO adapters ----
  | "ep_req0_valid",  1  => some (.reg 1  "mm0_req_valid")
  | "ep_req0_op",     1  => some (.reg 1  "mm0_req_op")
  | "ep_req0_cell",   9  => some (.reg 9  "mm0_cell")
  | "ep_req0_epoch",  32 => some (.reg 32 "mm0_epoch")
  | "ep_req0_policy", 1  => some (.reg 1  "mm0_req_policy")
  | "ep_req0_flags",  3  => some (.reg 3  "mm0_flags")
  | "ep_req1_valid",  1  => some (.reg 1  "mm1_req_valid")
  | "ep_req1_op",     1  => some (.reg 1  "mm1_req_op")
  | "ep_req1_cell",   9  => some (.reg 9  "mm1_cell")
  | "ep_req1_epoch",  32 => some (.reg 32 "mm1_epoch")
  | "ep_req1_policy", 1  => some (.reg 1  "mm1_req_policy")
  | "ep_req1_flags",  3  => some (.reg 3  "mm1_flags")
  -- ---- everything else is the dual's own wiring, unchanged ----
  | nm, ww => Machines.Lnp64mini.DualSoc.wire nm ww

/-- `lnp64mini_epoch = (c0 ∥ c1 ∥ arb ∥ hp ∥ gpm ∥ ep ∥ mm0 ∥ mm1).connect wire`. -/
def epochSoc : Design :=
  { (((((((c0.par c1).par arb).par hp).par gp).par ep).par mm0).par mm1).connect wire with
      name := "lnp64mini_epoch" }

/-- Pairwise `parOkB` over the eight instances (checked before emit). -/
def parOk : Bool :=
  let a1 := c0.par c1
  let a2 := a1.par arb
  let a3 := a2.par hp
  let a4 := a3.par gp
  let a5 := a4.par ep
  let a6 := a5.par mm0
  (c0.parOkB c1) && (a1.parOkB arb) && (a2.parOkB hp) && (a3.parOkB gp)
    && (a4.parOkB ep) && (a5.parOkB mm0) && (a6.parOkB mm1)

/-- The composed design keeps every memory D19 sync-read shaped: the
cores' `rf`/`dmem`/`uart_mem` and the engine's four banks. -/
def syncReadOk : Bool :=
  ["c0_rf", "c0_dmem", "c0_uart_mem", "c1_rf", "c1_dmem", "c1_uart_mem",
   "ep_cell_epoch", "ep_cell_flags", "ep_repl0", "ep_repl1"].all
    epochSoc.syncReadOkB

def syncReadReport : String :=
  String.intercalate "\n"
    (["c0_rf", "c0_dmem", "c0_uart_mem", "c1_rf", "c1_dmem", "c1_uart_mem",
      "ep_cell_epoch", "ep_cell_flags", "ep_repl0", "ep_repl1"].map
      epochSoc.syncReadReport)

end Machines.Epoch.EpochSoc
