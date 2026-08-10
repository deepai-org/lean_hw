-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Notation

/-!
# LNP64mini lightweight typed interface

Handles needed by both the core and external generated integrations live here
so those integrations do not duplicate names or widths and do not need to
construct the full machine.  This module contains declarations only: no rules,
semantics, simulation, or board behavior.
-/

namespace Machines.Lnp64mini

open Loom.Hw

/-- Architectural depth of thread-indexed memories. -/
def NTMEM : Nat := 32

def runningReg : Reg 1 := ⟨"running"⟩
def haltedReg : Reg 1 := ⟨"halted"⟩

def faultCauseReg : Reg 8 := ⟨"fault_cause"⟩
def faultPcReg : Reg 64 := ⟨"fault_pc"⟩
def faultCurReg : Reg 5 := ⟨"fault_cur"⟩

def traceRdPcReg : Reg 64 := ⟨"trace_rd_pc"⟩
def traceRdWbReg : Reg 64 := ⟨"trace_rd_wb"⟩

/-- Values supplied by the core's environment for one open-design cycle.
This is interface data, not a second machine state or transition function. -/
structure MiniIn where
  mDone    : Bool := false
  mRdata   : BitVec 64 := 0
  mBusy    : Bool := false
  gpDone   : Bool := false
  gpRdata  : BitVec 32 := 0
  gpBusy   : Bool := false
  cmdValid : Bool := false
  cmdIdx   : Nat  := 0
  cmdData  : BitVec 32 := 0
  resKill  : Bool := false
  doorbell : Bool := false
  doorbellKey : BitVec 64 := 0
  hold     : Bool := false
  scFail   : Bool := false
  deriving Repr

end Machines.Lnp64mini
