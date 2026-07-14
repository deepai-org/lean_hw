-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireRgn

/-!
# R-MC support: the `map` retirement arm

`map` caches a live memory capability's authority in a region register:
two errno outcomes (stale handle, bad cap — class mismatch or gate
kind) and the region-write outcome, whose packed value decodes to the
spec's cached `Region` through the kind-canon clause (`mapVal_pack`).
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

set_option maxHeartbeats 25600000
set_option maxRecDepth 400000

/-! ## Bit-level class/kind bridges -/

private theorem extract1_eq_iff {n m : Nat} (a : BitVec n) (b : BitVec m)
    (i j : Nat) :
    (a.extractLsb' i 1 = b.extractLsb' j 1) ↔ (a.getLsbD i = b.getLsbD j) := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec 1 => v.getLsbD 0) h
    simpa [BitVec.getLsbD_extractLsb'] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k
    simpa [BitVec.getLsbD_extractLsb'] using h

private theorem extract1_eq_zero_iff {n : Nat} (a : BitVec n) (i : Nat) :
    (a.extractLsb' i 1 = 0#1) ↔ (a.getLsbD i = false) := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec 1 => v.getLsbD 0) h
    simpa [BitVec.getLsbD_extractLsb'] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    interval_cases k
    simpa [BitVec.getLsbD_extractLsb'] using h

/-- Class agreement between a handle word and a kind word is the
tag-bit test. -/
private theorem cls_eq_iff_bits (hw kw : BitVec 32) :
    ((Handle.decode hw).cls = (Hw.decKind kw).cls)
      ↔ (hw.getLsbD 12 = kw.getLsbD 0) := by
  rw [show (Handle.decode hw).cls
    = (if hw.getLsbD 12 then CapClass.gate else CapClass.mem) from rfl]
  rw [Hw.decKind]
  cases h1 : hw.getLsbD 12 <;> cases h2 : kw.getLsbD 0 <;>
    simp [CapKind.cls]

/-- The memory-kind test is the tag bit. -/
private theorem decKind_mem_iff (kw : BitVec 32) :
    (kw.getLsbD 0 = false) ↔
      Hw.decKind kw = .mem (kw.extractLsb' 1 12) (kw.extractLsb' 13 13)
        (Hw.decPerms (kw.extractLsb' 26 3)) := by
  rw [Hw.decKind]
  cases h : kw.getLsbD 0 <;> simp

end Machines.Lnp64u.Theorems.RMC
