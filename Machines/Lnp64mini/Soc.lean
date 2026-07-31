-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.Core
import Machines.Lnp64mini.HpMaster
import Machines.Lnp64mini.GpMaster
import Loom.Hw.Compose

/-!
# lnp64mini SoC — the all-Lean composed system

`soc = core ∥ hp ∥ gp`, wired with `Design.connect` so the two AXI masters
and the HP ownership mux — previously live Verilog in `lnp64mini_top.v` —
now live inside the emitted design. The only remaining soc inputs are the
AXI slave responses (`hp_m_awready`, …, `gp_m_rvalid`, …) and the cmd
surface (`cmd_valid`/`cmd_idx`/`cmd_data`) driven by the thin wrapper.

## Composition (COMPOSE_SPEC.md §4)

* `core`   — the existing `Machines.Lnp64mini.design` value, UNMODIFIED
  (no prefix; keeps its `o_*` observability names for the wrapper's BSCAN
  read map).
* `hp`     — `HpMaster.design.prefixed "hp_"`.
* `gp`     — `GpMaster.design.prefixed "gp_"`.

Connect wiring (combinational same-cycle Verilog port connections):

Core master-response inputs ← master status registers:
  `m_done  ← hp_done`,  `m_rdata ← hp_rdata`,  `m_busy ← hp_busy`,
  `gp_done ← gp_done`,  `gp_rdata ← gp_rdata`, `gp_busy ← gp_busy`.

HP master control inputs ← the ownership mux over core state
  (`hp_core_owns = running ∧ st∉{S_TRAP,S_WAIT,S_PAUSE}` absorbed here):
  `hp_start_wr ← owns?core_wr:jtag_wr`, `hp_start_rd ← owns?core_rd:jtag_rd`,
  `hp_addr ← owns?core_addr:ddr_addr_j`, `hp_wdata ← owns?core_wdata:jtag_wdata`.

GP master control inputs ← core GP request registers:
  `gp_start_wr ← gp_wr`, `gp_start_rd ← gp_rd`,
  `gp_addr ← gp_addr_r`, `gp_wdata ← gp_wdata_r`.
-/

namespace Machines.Lnp64mini.Soc

open Loom.Hw
open Machines.Lnp64mini (design S_TRAP S_WAIT S_PAUSE)

/-! ## Ownership mux (absorbed from the wrapper) -/

/-- `hp_core_owns = running && st∉{S_TRAP,S_WAIT,S_PAUSE}`, over core regs. -/
def owns : Expr 1 :=
  .and (.reg 1 "running")
    (.and (.not (.eq (.reg 5 "st") (.lit (BitVec.ofNat 5 S_TRAP))))
      (.and (.not (.eq (.reg 5 "st") (.lit (BitVec.ofNat 5 S_WAIT))))
            (.not (.eq (.reg 5 "st") (.lit (BitVec.ofNat 5 S_PAUSE))))))

/-! ## The three instances -/

def core : Design := design
def hp   : Design := HpMaster.design.prefixed "hp_"
-- NOTE: prefix "gpm_" (not "gp_") — the core already owns input coordinates
-- named `gp_done`/`gp_rdata`/`gp_busy` and registers `gp_rd`/`gp_wr`/…, so a
-- "gp_" prefix on the master would collide with them under `par`. See the
-- COMPOSE_SPEC "## Deviations" note.
def gp   : Design := GpMaster.design.prefixed "gpm_"

/-! ## Connect wiring -/

/-- The soc wire function: for each input name, `some e` connects it to the
same-cycle expression `e`; `none` leaves it a soc input. -/
def wire (n : String) (w : Nat) : Option (Expr w) :=
  -- widths are known statically; we match name then coerce the literal reg
  -- expression to the requested width via `if h : w = _`.
  match n, w with
  -- core master-response inputs ← HP master status registers
  | "m_done",   1  => some (.reg 1  "hp_done")
  | "m_rdata",  64 => some (.reg 64 "hp_rdata")
  | "m_busy",   1  => some (.reg 1  "hp_busy")
  -- core GP-response inputs ← GP master status registers
  | "gp_done",  1  => some (.reg 1  "gpm_done")
  | "gp_rdata", 32 => some (.reg 32 "gpm_rdata")
  | "gp_busy",  1  => some (.reg 1  "gpm_busy")
  -- HP master control inputs ← ownership mux over core state
  | "hp_start_wr", 1  => some (.mux owns (.reg 1  "core_wr")    (.reg 1  "jtag_wr"))
  | "hp_start_rd", 1  => some (.mux owns (.reg 1  "core_rd")    (.reg 1  "jtag_rd"))
  | "hp_addr",     32 => some (.mux owns (.reg 32 "core_addr")  (.reg 32 "ddr_addr_j"))
  | "hp_wdata",    64 => some (.mux owns (.reg 64 "core_wdata") (.reg 64 "jtag_wdata"))
  -- GP master control inputs ← core GP request registers
  | "gpm_start_wr", 1  => some (.reg 1  "gp_wr")
  | "gpm_start_rd", 1  => some (.reg 1  "gp_rd")
  | "gpm_addr",     32 => some (.reg 32 "gp_addr_r")
  | "gpm_wdata",    32 => some (.reg 32 "gp_wdata_r")
  -- SMP extension inputs are tied off in the SINGLE-core soc, so the
  -- emitted module keeps exactly its pre-SMP port list (the §63 wrapper and
  -- the whole NetBSD flow are unchanged).
  | "res_kill",     1  => some (.lit 0)
  | "doorbell",     1  => some (.lit 0)
  | "hold",         1  => some (.lit 0)
  | "sc_fail",      1  => some (.lit 0)
  | _, _ => none

/-- `soc = (core ∥ hp ∥ gp).connect wire`. -/
def soc : Design :=
  { (((core.par hp).par gp).connect wire) with name := "lnp64mini_soc" }

/-! ## Composition sanity: `parOkB` holds for the three instances. -/

/-- The three instances have disjoint owned names and rule names. Checked at
`#eval`/emit time. -/
def parOk : Bool := (core.parOkB hp) && ((core.par hp).parOkB gp)

end Machines.Lnp64mini.Soc
