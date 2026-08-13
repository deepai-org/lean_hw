-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.HpMaster
import Machines.Lnp64mini.GpMaster
import Machines.Lnp64mini.HpArbiter
import Loom.Hw.Compose

/-!
# lnp64mini_dual — the two-core SMP SoC (DUAL_SPEC.md)

```
dual = (core.prefixed "c0_") ∥ (core.prefixed "c1_")
     ∥ (HpArbiter.prefixed "arb_") ∥ (HpMaster.prefixed "hp_")
     ∥ (GpMaster.prefixed "gpm_")
```

## Memory model

Both cores reach DDR through **one** `HpArbiter` in front of **one**
`HpMaster`, and the DDR is uncached. The arbiter therefore *is* the
serialization point: every load, store and instruction fetch from either
core occupies the single downstream master alone, so the observable
execution is some interleaving of the two cores' memory operations, and all
cores agree on it — **sequential consistency** over shared DDR, for free.

Everything else is core-private ABI and is *not* shared, by construction:

* `rf` (1024 × 64) and the zero-page `dmem` (512 × 64) are per-core BRAMs;
  a zero-page address (`ea < 0x1000`) never leaves the core.
* the UART TX ring (`uart_mem`) and RX ring (`rx_mem`) are per-core, and so
  are `uart_wptr`/`rx_wptr`/`rx_rptr` — each core has its own console.
* the 32 thread slots (`tpc`/`tstate`/`tsleep`/`tfutex`/…) are per-core: a
  thread never migrates. Cross-core scheduling is the `doorbell`.

**All shared data lives in DDR** (`ea ≥ 0x1000`), which is the only address
space both cores can see.

## Cross-core wiring

* `arb_c{i}_*` ← core `i`'s request registers. Core 0 keeps the JTAG DDR
  window (it owns the loader), so its arbiter port is the *existing*
  ownership mux `owns0 ? core_* : jtag_*`; core 1 drives its port directly.
  JTAG requests and core-1 requests simply interleave through the arbiter,
  so no global "both cores yield" gate is needed (see Deviations).
* `c{i}_m_done`/`c{i}_m_rdata` ← the arbiter's per-core response registers,
  so each core only ever sees its **own** completions (and core 0's
  `ddr_rd_l` JTAG latch keeps working unchanged).
* `c{i}_res_kill` ← `arb_res_kill{i}`, and the global-LR/SC tag/verdict
  triple `arb_c{i}_lr`/`arb_c{i}_sc` ← `c{i}_lr_req`/`c{i}_sc_req`,
  `c{i}_sc_fail` ← `arb_c{i}_sc_fail` (see `HpArbiter`).
* `c0_doorbell` ← `c1_wake_out` and `c1_doorbell` ← `c0_wake_out`. Both are
  register-output→input connections, i.e. already a full register stage:
  there is **no combinational cross-core path** and no extra glue design is
  needed.
* `c0_hold` is tied 0; `c1_hold` stays a SoC input (CORE1_HOLD in the
  wrapper). The debug wrapper may OR a generated first-event halt request into
  core 1's instruction-boundary hold without changing core state.
* GP/GEM belongs to core 0 (`gpm_*` ← `c0_gp_*`). Core 1's GP responses are
  tied to "instantly done, reads 0", so a stray core-1 GP access completes
  harmlessly instead of wedging the core.
-/

namespace Machines.Lnp64mini.DualSoc

open Loom.Hw
open Machines.Lnp64mini (design S_TRAP S_WAIT S_PAUSE)

/-! ## Ownership mux for core 0's JTAG DDR window -/

/-- `hp_core_owns` for core `i`: `running ∧ st ∉ {S_TRAP,S_WAIT,S_PAUSE}`. -/
def owns (p : String) : Expr 1 :=
  .and (.reg 1 (p ++ "running"))
    (.and (.not (.eq (.reg 5 (p ++ "st")) S_TRAP))
      (.and (.not (.eq (.reg 5 (p ++ "st")) S_WAIT))
            (.not (.eq (.reg 5 (p ++ "st")) S_PAUSE))))

def owns0 : Expr 1 := owns "c0_"

/-! ## The five instances -/

def c0  : Design := design.prefixed "c0_"
def c1  : Design := design.prefixed "c1_"
def arb : Design := HpArbiter.design.prefixed "arb_"
def hp  : Design := HpMaster.design.prefixed "hp_"
def gp  : Design := GpMaster.design.prefixed "gpm_"

/-! ## Connect wiring -/

def wire (n : String) (w : Nat) : Option (Expr w) :=
  match n, w with
  -- ---- core master-response inputs ← the arbiter's per-core routing ----
  | "c0_m_done",   1  => some (.reg 1  "arb_c0_done")
  | "c0_m_rdata",  64 => some (.reg 64 "arb_c0_rdata")
  | "c0_m_busy",   1  => some (.reg 1  "arb_busy")
  | "c1_m_done",   1  => some (.reg 1  "arb_c1_done")
  | "c1_m_rdata",  64 => some (.reg 64 "arb_c1_rdata")
  | "c1_m_busy",   1  => some (.reg 1  "arb_busy")
  -- ---- SMP extension inputs ----
  | "c0_res_kill", 1  => some (.reg 1 "arb_res_kill0")
  | "c1_res_kill", 1  => some (.reg 1 "arb_res_kill1")
  -- cross doorbells: register output -> input = a registered stage
  | "c0_doorbell", 1  => some (.reg 1 "c1_wake_out")
  | "c1_doorbell", 1  => some (.reg 1 "c0_wake_out")
  -- EXT-4: the key travels with the doorbell so the shared wake bank can be
  -- keyed. Register output -> input, same registered stage as the pulse.
  | "c0_doorbell_key", 64 => some (.reg 64 "c1_wake_key")
  | "c1_doorbell_key", 64 => some (.reg 64 "c0_wake_key")
  | "c0_hold",     1  => some (.lit 0)          -- core 0 always runs
  -- "c1_hold" stays a SoC input (CORE1_HOLD/debug hold)
  -- ---- arbiter requester port 0 ← core 0 (with the JTAG ownership mux) ----
  | "arb_c0_rd",    1  => some (.mux owns0 (.reg 1  "c0_core_rd")    (.reg 1  "c0_jtag_rd"))
  | "arb_c0_wr",    1  => some (.mux owns0 (.reg 1  "c0_core_wr")    (.reg 1  "c0_jtag_wr"))
  | "arb_c0_addr",  32 => some (.mux owns0 (.reg 32 "c0_core_addr")  (.reg 32 "c0_ddr_addr_j"))
  | "arb_c0_wdata", 64 => some (.mux owns0 (.reg 64 "c0_core_wdata") (.reg 64 "c0_jtag_wdata"))
  -- ---- arbiter requester port 1 ← core 1 (no JTAG DDR window) ----
  | "arb_c1_rd",    1  => some (.reg 1  "c1_core_rd")
  | "arb_c1_wr",    1  => some (.reg 1  "c1_core_wr")
  | "arb_c1_addr",  32 => some (.reg 32 "c1_core_addr")
  | "arb_c1_wdata", 64 => some (.reg 64 "c1_core_wdata")
  -- ---- global LR/SC tags + verdict ----
  | "arb_c0_lr", 1 => some (.reg 1 "c0_lr_req")
  | "arb_c0_sc", 1 => some (.reg 1 "c0_sc_req")
  | "arb_c1_lr", 1 => some (.reg 1 "c1_lr_req")
  | "arb_c1_sc", 1 => some (.reg 1 "c1_sc_req")
  | "c0_sc_fail", 1 => some (.reg 1 "arb_c0_sc_fail")
  | "c1_sc_fail", 1 => some (.reg 1 "arb_c1_sc_fail")
  -- ---- arbiter ↔ HP master ----
  | "arb_m_done",  1  => some (.reg 1  "hp_done")
  | "arb_m_rdata", 64 => some (.reg 64 "hp_rdata")
  | "hp_start_wr", 1  => some (.reg 1  "arb_d_start_wr")
  | "hp_start_rd", 1  => some (.reg 1  "arb_d_start_rd")
  | "hp_addr",     32 => some (.reg 32 "arb_d_addr")
  | "hp_wdata",    64 => some (.reg 64 "arb_d_wdata")
  -- ---- GP master: core 0 only ----
  | "c0_gp_done",  1  => some (.reg 1  "gpm_done")
  | "c0_gp_rdata", 32 => some (.reg 32 "gpm_rdata")
  | "c0_gp_busy",  1  => some (.reg 1  "gpm_busy")
  | "c1_gp_done",  1  => some (.lit 1)    -- core 1: GP completes instantly…
  | "c1_gp_rdata", 32 => some (.lit 0)    -- …reading 0 (no wedge, no GEM)
  | "c1_gp_busy",  1  => some (.lit 0)
  | "gpm_start_wr", 1  => some (.reg 1  "c0_gp_wr")
  | "gpm_start_rd", 1  => some (.reg 1  "c0_gp_rd")
  | "gpm_addr",     32 => some (.reg 32 "c0_gp_addr_r")
  | "gpm_wdata",    32 => some (.reg 32 "c0_gp_wdata_r")
  | _, _ => none

/-- `dual = (c0 ∥ c1 ∥ arb ∥ hp ∥ gp).connect wire`. -/
def dual : Design :=
  { ((((c0.par c1).par arb).par hp).par gp).connect wire with
      name := "lnp64mini_dual" }

/-- Pairwise `parOkB` over the five instances (checked before emit). -/
def parOk : Bool :=
  (c0.parOkB c1)
  && ((c0.par c1).parOkB arb)
  && (((c0.par c1).par arb).parOkB hp)
  && ((((c0.par c1).par arb).par hp).parOkB gp)

end Machines.Lnp64mini.DualSoc
