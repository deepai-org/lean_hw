-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.CapWalk.Engine
import Machines.Epoch.EpochSoc
import Loom.Hw.Compose

/-!
# `lnp64mini_cap` — the capability engine **beside** the epoch engine

```
lnp64mini_cap = c0 ∥ c1 ∥ arb ∥ hp ∥ gpm ∥ ep ∥ mm0 ∥ mm1 ∥ cw ∥ cwhp ∥ cm0
                └──────────── Machines/Epoch/EpochSoc ────────────┘ └── new ──┘
```

`Machines/Lnp64mini/{Soc,DualSoc}.lean` and `Machines/Epoch/*` are **not
edited**, so `lnp64mini{,_soc,_dual}.v` and `lnp64mini_epoch.v` stay
byte-identical; this file adds three instances and the seam.

## Engine #2 lands on engine #1

`CAPWALK_SPEC.md`: "§2.2's two invalidation mechanisms, the slot's embedded
cell and the shared lineage cell, *are* §3 epoch cells. Engine #2 lands on
engine #1." Concretely, and with no edit to the epoch engine:

* the **embedded** cells are the capability engine's own on-chip
  `cell_epoch`/`cell_flags` (they carry occupancy, which §3's alphabet has
  no transition for — Layer-1 C9 says exactly this);
* the **lineage** cells are the epoch engine's. `cap_revoke` is a §3 bump
  requested through the *existing* `epochmmio` word, and the capability
  engine is one more **referent volume** of it: `cw_inval_*` ←
  `ep_inval_*`, and `lin_repl` is written only by that broadcast. No core
  can write a lineage replica, and there is no address a core can name that
  reaches one (deviation CE7).

## The seam

Core 0's GP aperture already carves out `0x0A0E_0000` for the epoch engine
(`EpochSoc`). One more 4 KiB page, **`0x0A0D_0000`**, is carved out for the
capability engine, so `c0_gp_done`/`c0_gp_rdata` become a three-way mux and
the AXI GP master is gated off both engine pages.

Word map (byte offsets from `0x0A0D_0000`, 32-bit accesses):

| off | write | read |
|-----|-------|------|
| 0x00 | slot index (24 bits of the handle) | slot |
| 0x04 | presented epoch (the handle's epoch field) | epoch |
| 0x08 | `{wf<<16, cls<<8, need}` | same |
| 0x0C | `{len<<16, off}` | same |
| 0x10 | **fire CHECK** | `{chk_pend, chk_busy}` |
| 0x14 | — | **RESULT** `{valid<<8, outcome code}` — *blocks* until the check answers |
| 0x18 | **fire OP** (1 = drop, 2 = re-incarnate) | — |
| 0x1C | — | fills that authenticated |
| 0x20 | — | fills that did **not** (the fail-stop counter) |
| 0x24 | — | last fill latency, in cycles |
| 0x28 | — | the slot the last fail-stop named |
| else | — | ID `0xCA9C0001` |

Note what is *not* in that table: there is no word that writes a cache line,
a tag, a cell epoch, a fault bit, a lineage replica or the MAC key. The
adapter stages a **decoded handle** and fires a request; everything else the
engine owns.

## DDR

The capability table is DDR-resident and reached through its **own**
`axi_hp_master` (`cwhp_`), not through the cores' arbiter: `HpArbiter` has
exactly two requester ports and both are spoken for, and the ZC702 has four
HP ports. Read-only — v1's engine never writes the table (deviation CE8) —
so `cwhp_start_wr`/`cwhp_wdata` are tied off and the master's write path
constant-folds away.
-/

namespace Machines.CapWalk.CapSoc

-- see EpochSoc: `actSeq` also lives in Loom.Hw (Trees.lean)
open Loom.Hw hiding actSeq
open Machines.CapWalk.Engine (Cfg cfg32 SLOTB actSeq L1 L2 L3 L16)

/-! ## `capmmio` — the per-core GP-transaction adapter -/

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

def qActive : Expr 1 := .reg 1 "q_active"
def qIdx : Expr 4 := .reg 4 "q_idx"
def chkPend : Expr 1 := .reg 1 "chk_pend"
def resV : Expr 1 := .reg 1 "res_v"
def resCode : Expr 3 := .reg 3 "res_code"

/-- 4-bit literal. -/
def L4 (n : Nat) : Expr 4 := .lit (BitVec.ofNat 4 n)

/-- The transaction's word index, `addr[5:2]`. -/
def idxE : Expr 4 := .slice gpAddr 2 4
def idxIs (n : Nat) : Expr 4 → Expr 1 := fun e => .eq e (L4 n)

def readMux : Expr 32 :=
  .mux (idxIs 0 qIdx) (.zext (.reg SLOTB "slot") 32) <|
  .mux (idxIs 1 qIdx) (.zext (.reg cfg.ew "epoch") 32) <|
  .mux (idxIs 2 qIdx)
    (.or (.or (.zext (.reg 8 "need") 32) (.shl (.zext (.reg 8 "cls") 32) (.lit 8)))
         (.shl (.zext (.reg 1 "wf") 32) (.lit 16))) <|
  .mux (idxIs 3 qIdx)
    (.or (.zext (.reg 16 "off") 32) (.shl (.zext (.reg 16 "len") 32) (.lit 16))) <|
  .mux (idxIs 4 qIdx)
    (.or (.shl (.zext chkPend 32) (.lit 1)) (.zext chkBusy 32)) <|
  .mux (idxIs 5 qIdx)
    (.or (.shl (.zext resV 32) (.lit 8)) (.zext resCode 32)) <|
  .mux (idxIs 7 qIdx) (.zext (.reg 16 "fill_count") 32) <|
  .mux (idxIs 8 qIdx) (.zext (.reg 16 "fault_count") 32) <|
  .mux (idxIs 9 qIdx) (.zext (.reg 16 "fill_cycles") 32) <|
  .mux (idxIs 10 qIdx) (.zext (.reg SLOTB "fault_slot") 32) (.lit 0xCA9C0001)

/-- A pending RESULT read blocks until the check unit has answered — §2.2's
check exposed as a load that completes exactly when the verdict exists. -/
def stallE : Expr 1 :=
  .and (idxIs 5 qIdx) (.or (.or chkPend chkBusy) respValid)

def body : Act :=
  actSeq [
    .write 1 "done" (L1 0),
    .write 1 "req_valid" (L1 0),
    -- the engine's response lands here; the core never writes it
    .ite respValid
      (actSeq [ .write 3 "res_code" respCode, .write 1 "res_v" (L1 1),
                .write 1 "chk_pend" (L1 0) ]) .skip,
    -- accept one GP transaction
    .ite (.and (.and (.or gpRd gpWr) sel) (.not qActive))
      (actSeq [
        .write 4 "q_idx" idxE,
        .write 1 "q_active" (L1 1),
        .ite gpWr
          (.ite (idxIs 0 idxE) (.write SLOTB "slot" (.slice gpWdata 0 SLOTB)) <|
           .ite (idxIs 1 idxE) (.write cfg.ew "epoch" (.slice gpWdata 0 cfg.ew)) <|
           .ite (idxIs 2 idxE)
             (actSeq [ .write 8 "need" (.slice gpWdata 0 8),
                       .write 8 "cls" (.slice gpWdata 8 8),
                       .write 1 "wf" (.slice gpWdata 16 1) ]) <|
           .ite (idxIs 3 idxE)
             (actSeq [ .write 16 "off" (.slice gpWdata 0 16),
                       .write 16 "len" (.slice gpWdata 16 16) ]) <|
           .ite (idxIs 4 idxE)
             (actSeq [ .write 1 "req_valid" (L1 1), .write 2 "req_op" (L2 0),
                       .write 1 "chk_pend" (L1 1) ]) <|
           .ite (idxIs 6 idxE)
             (actSeq [ .write 1 "req_valid" (L1 1),
                       .write 2 "req_op" (.slice gpWdata 0 2) ])
             .skip)
          .skip ])
      .skip,
    -- complete it when the engine is ready
    .ite (.and qActive (.not (stallE)))
      (actSeq [
        .write 1 "done" (L1 1),
        .write 32 "rdata" (readMux cfg),
        .write 1 "q_active" (L1 0),
        .ite (idxIs 5 qIdx) (.write 1 "res_v" (L1 0)) .skip ])
      .skip ]

def design : Design where
  name := "capmmio"
  regs :=
    [ ⟨"slot", SLOTB, 0⟩, ⟨"epoch", cfg.ew, 1⟩, ⟨"need", 8, 0⟩,
      ⟨"cls", 8, 1⟩, ⟨"wf", 1, 1⟩, ⟨"off", 16, 0⟩, ⟨"len", 16, 1⟩,
      ⟨"req_valid", 1, 0⟩, ⟨"req_op", 2, 0⟩,
      ⟨"rdata", 32, 0⟩, ⟨"done", 1, 0⟩,
      ⟨"res_code", 3, 0⟩, ⟨"res_v", 1, 0⟩, ⟨"chk_pend", 1, 0⟩,
      ⟨"q_active", 1, 0⟩, ⟨"q_idx", 4, 0⟩ ]
  mems := []
  -- D39a: outputs are mandatory and explicit, like inputs.
  outputs :=
    [ "slot", "epoch", "need", "cls", "wf", "off", "len", "req_valid",
      "req_op", "rdata", "done", "res_code", "res_v", "chk_pend",
      "q_active", "q_idx" ]
  rules := [⟨"capmmio", body cfg⟩]
  inputs :=
    [ ⟨"gp_rd", 1⟩, ⟨"gp_wr", 1⟩, ⟨"gp_addr", 32⟩, ⟨"gp_wdata", 32⟩,
      ⟨"sel", 1⟩, ⟨"resp_valid", 1⟩, ⟨"resp_code", 3⟩, ⟨"chk_busy", 1⟩,
      ⟨"fill_count", 16⟩, ⟨"fault_count", 16⟩, ⟨"fill_cycles", 16⟩,
      ⟨"fault_slot", SLOTB⟩ ]

end Mmio

/-! ## Instances -/

open Machines.Lnp64mini.DualSoc (c0 c1 arb hp gp)
open Machines.Epoch.EpochSoc (ep mm0 mm1 epSel)

/-- The capability engine, prefixed `cw_`. -/
def cw : Design := Machines.CapWalk.Engine.design.prefixed "cw_"
/-- The capability engine's own HP master (a second HP port). -/
def cwhp : Design := Machines.Lnp64mini.HpMaster.design.prefixed "cwhp_"
/-- Core 0's capability-MMIO adapter. -/
def cm0 : Design := (Mmio.design cfg32).prefixed "cm0_"

/-- The capability-engine page: `gp_addr[31:12] == 0x0A0D0`. -/
def CAP_PAGE : Nat := 0x0A0D0

/-- Where the DDR-resident capability table lives (integration-time
constant, driven onto the engine's `tbl_base` port; not core-writable). -/
def CAP_TBL_BASE : Nat := 0x1000_0000

/-- Aperture decode over core `k`'s latched GP address. -/
def capSel (k : Nat) : Expr 1 :=
  .eq (.slice (.reg 32 s!"c{k}_gp_addr_r") 12 20) (.lit (BitVec.ofNat 20 CAP_PAGE))

/-! ## Wiring

Everything `Machines.Epoch.EpochSoc.wire` does (and therefore everything
`DualSoc.wire` does), plus the capability seam. The four GP entries that
change are listed *before* the delegation. -/

def wire (n : String) (w : Nat) : Option (Expr w) :=
  match n, w with
  -- ---- core 0's GP response: two engine pages, else the AXI GP master ----
  | "c0_gp_done", 1 => some
      (.mux (epSel 0) (.reg 1 "mm0_done")
        (.mux (capSel 0) (.reg 1 "cm0_done") (.reg 1 "gpm_done")))
  | "c0_gp_rdata", 32 => some
      (.mux (epSel 0) (.reg 32 "mm0_rdata")
        (.mux (capSel 0) (.reg 32 "cm0_rdata") (.reg 32 "gpm_rdata")))
  -- the AXI GP master must not see an engine-page transaction
  | "gpm_start_wr", 1 => some
      (.and (.reg 1 "c0_gp_wr") (.not (.or (epSel 0) (capSel 0))))
  | "gpm_start_rd", 1 => some
      (.and (.reg 1 "c0_gp_rd") (.not (.or (epSel 0) (capSel 0))))
  -- ---- the capability MMIO adapter ← core 0's GP request registers ----
  | "cm0_gp_rd",    1  => some (.reg 1  "c0_gp_rd")
  | "cm0_gp_wr",    1  => some (.reg 1  "c0_gp_wr")
  | "cm0_gp_addr",  32 => some (.reg 32 "c0_gp_addr_r")
  | "cm0_gp_wdata", 32 => some (.reg 32 "c0_gp_wdata_r")
  | "cm0_sel",      1  => some (capSel 0)
  -- ---- the adapter ← the engine's response/observability ----
  | "cm0_resp_valid", 1  => some (.reg 1  "cw_resp_valid")
  | "cm0_resp_code",  3  => some (.reg 3  "cw_resp_code")
  | "cm0_chk_busy",   1  => some (.reg 1  "cw_k_busy")
  | "cm0_fill_count", 16 => some (.reg 16 "cw_fill_count")
  | "cm0_fault_count",16 => some (.reg 16 "cw_fault_count")
  | "cm0_fill_cycles",16 => some (.reg 16 "cw_fill_cycles")
  | "cm0_fault_slot", 24 => some (.reg 24 "cw_fault_slot")
  -- ---- the engine's request port ← the adapter ----
  | "cw_req_valid", 1  => some (.reg 1  "cm0_req_valid")
  | "cw_req_op",    2  => some (.reg 2  "cm0_req_op")
  | "cw_req_slot",  24 => some (.reg 24 "cm0_slot")
  | "cw_req_epoch", 32 => some (.reg 32 "cm0_epoch")
  | "cw_req_need",  8  => some (.reg 8  "cm0_need")
  | "cw_req_cls",   8  => some (.reg 8  "cm0_cls")
  | "cw_req_off",   16 => some (.reg 16 "cm0_off")
  | "cw_req_len",   16 => some (.reg 16 "cm0_len")
  | "cw_req_wf",    1  => some (.reg 1  "cm0_wf")
  -- ---- the engine ← the epoch engine's §3 broadcast (engine #2 on #1) ----
  | "cw_inval_valid", 1  => some (.reg 1  "ep_inval_valid")
  | "cw_inval_cell",  9  => some (.reg 9  "ep_inval_cell")
  | "cw_inval_epoch", 32 => some (.reg 32 "ep_inval_epoch")
  -- ---- the engine ↔ its own HP master ----
  | "cw_m_done",   1  => some (.reg 1  "cwhp_done")
  | "cw_m_rdata",  64 => some (.reg 64 "cwhp_rdata")
  | "cw_tbl_base", 32 => some (.lit (BitVec.ofNat 32 CAP_TBL_BASE))
  | "cwhp_start_rd", 1  => some (.reg 1  "cw_m_start_rd")
  | "cwhp_start_wr", 1  => some (.lit 0)          -- v1 never writes the table
  | "cwhp_addr",     32 => some (.reg 32 "cw_m_addr")
  | "cwhp_wdata",    64 => some (.lit 0)
  -- ---- everything else is the epoch SoC's own wiring, unchanged ----
  | nm, ww => Machines.Epoch.EpochSoc.wire nm ww

/-- `lnp64mini_cap = (c0 ∥ c1 ∥ arb ∥ hp ∥ gpm ∥ ep ∥ mm0 ∥ mm1 ∥ cw ∥ cwhp ∥ cm0).connect wire`. -/
def capSoc : Design :=
  { ((((((((((c0.par c1).par arb).par hp).par gp).par ep).par mm0).par mm1).par
        cw).par cwhp).par cm0).connect wire with
      name := "lnp64mini_cap" }

/-- Pairwise `parOkB` over the eleven instances (checked before emit). -/
def parOk : Bool :=
  let a1 := c0.par c1
  let a2 := a1.par arb
  let a3 := a2.par hp
  let a4 := a3.par gp
  let a5 := a4.par ep
  let a6 := a5.par mm0
  let a7 := a6.par mm1
  let a8 := a7.par cw
  let a9 := a8.par cwhp
  (c0.parOkB c1) && (a1.parOkB arb) && (a2.parOkB hp) && (a3.parOkB gp)
    && (a4.parOkB ep) && (a5.parOkB mm0) && (a6.parOkB mm1) && (a7.parOkB cw)
    && (a8.parOkB cwhp) && (a9.parOkB cm0)

/-- The banks the composed design must keep D19 sync-read shaped. -/
def banks : List String :=
  ["c0_rf", "c0_dmem", "c0_uart_mem", "c1_rf", "c1_dmem", "c1_uart_mem",
   "ep_cell_epoch", "ep_cell_flags", "ep_repl0", "ep_repl1",
   "cw_cell_epoch", "cw_cell_flags", "cw_c_tag", "cw_c_p0", "cw_c_p1",
   "cw_lin_repl"]

def syncReadOk : Bool := banks.all capSoc.syncReadOkB

def syncReadReport : String :=
  String.intercalate "\n" (banks.map capSoc.syncReadReport)

end Machines.CapWalk.CapSoc
