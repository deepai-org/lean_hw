-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Logic.Inflight
import Machines.Lnp64u.Logic.Hostage
import Machines.Lnp64u.Theorems.RMCAbs
import Machines.Lnp64u.Theorems.RMCResetDom
import Machines.Lnp64u.Theorems.RMCFrames
import Machines.Lnp64u.Theorems.RMCCanon
import Machines.Lnp64u.Theorems.RMCCountdown
import Machines.Lnp64u.Theorems.RMCIdle
import Machines.Lnp64u.Theorems.RMCIssue
import Machines.Lnp64u.Theorems.RMCZero
import Machines.Lnp64u.Theorems.RMCRetireSw
import Machines.Lnp64u.Theorems.RMCRetireRgn

/-!
# R-MC — the LNP64-µ EDSL core refines the ISS

The machine-code refinement theorem: the EDSL core (`Hw.core m`, 1 hardware
cycle = 1 spec cycle) tracks the ISS (`machine m` = `Step.step` iterated)
exactly through the abstraction function `Hw.abs` of `Hw/Enc.lean`. This is
what transports T2–T9 from the ISS onto the emitted Verilog (text side via
the parser round-trip, tool side via the µVerilog tool-boundary assumption).

## The statement is now the *unbounded* lockstep (resolved 2026-07-04)

Until 2026-07-04 the refinement was stated on the `n < 2 ^ 32` horizon,
because the unbounded form was **uninhabited**: `MachineState.cycle` was a
`Nat`, strictly increasing at every spec step, so `machine m` had no
periodic points — while every forward orbit of `(core m).cycle` is
eventually periodic (finitely many declared registers + finite RAM). A
`Simulation.square` is a functional-graph homomorphism and would map a
concrete periodic orbit to a spec periodic orbit; contradiction.

**Resolution (D-class, user decision 2026-07-04): the spec counter is the
hardware counter.** `MachineState.cycle` is now a `BitVec 32` that wraps at
`2 ^ 32` exactly like the RTL register — the `Nat` counter was non-physical.
The proof-forced companion is `Manifest.WF.period_dvd` (`periodP ∣ 2 ^ 32`
per domain): the refill cadence `cycle % P = 0` stays `P`-periodic across
the wrap only under that divisibility — the same constraint real RTOS tick
periods have against a free-running hardware timer. With it, the hidden
mod-`P` counters (`Coupled.rctr_sync`) stay in sync *through* the wrap
(`(2 ^ 32 - 1) + 1 ≡ 0` and `rctr` rolls `P - 1 → 0` simultaneously), so the
old `hwrap` side conditions on `square`/`coupled_step` are gone.

What is stated here, all horizon-free:

* `square` — one core cycle = one spec step through `Hw.abs`, under the
  hidden-state coupling `Coupled`, datapath-fit `Fits`, and reachability on
  both sides. The per-field, per-opcode workhorse.
* `abs_run` (**the R-MC headline**) — for *every* `n`,
  `Hw.abs ((core m).run n reset) = stepN m n m.initState`: exact
  whole-state lockstep from reset, forever — through counter wraps. The
  formal generalization of the 2000-cycle `Tests/Lnp64uCore.lean` run.
* `refines` — the unbounded `Simulation` onto the ISS, with `Hw.abs` as the
  abstraction function, for the core *on its boot orbit* (`reachCore`, the
  same states/reset with the step exercised from reachable states — which
  is every state the powered-on device ever occupies, and reachability
  coincides with `(core m).toTSys`'s, `reachCore_reachable_iff`). The
  restriction is inherent, not a wrap artifact: `square` is conditioned on
  the physical coupling invariant `Coupled` (hidden refill counters in sync,
  canonical encodings), and garbage register files outside the boot orbit
  satisfy neither it nor the range invariants the per-opcode arms need. A
  full-state-space simulation would need a commuting abstraction for
  arbitrary junk states, which carries no verification content — every
  invariant transport already factors through reachable states
  (`invariant_transport`).
* `invariant_transport` — every ISS invariant (T2–T9's currency) holds of
  the abstraction of every core state, at every cycle count. Sorry-free
  given `square`/`coupled_step` (the two remaining sorries below).

## Landed support (sorry-free)

* `RMCEnc.lean` — every encoder/decoder round trip (`decKind_encKind`,
  `decRegion_encRegion`, `decRef_encRef`/`encRef_decRef`, `decRun_encRun`,
  `decPerms_encPerms`, `finOfBv_ofNat`).
* `RMCReset.lean` / `RMCResetDeclList.lean` / `RMCResetCanon.lean` /
  `RMCResetDom.lean` — reset lookups for the 825-register file with a
  symbolic manifest: name distinctness checked in the kernel on a
  precomputed `Nat` key list (no string comparisons), `foldl_set_get`
  (last write wins), `reset_lookup i` (the register's name, width, and
  declared init all reduce definitionally), `reset_mem`, reset canonical
  encoding facts, and every domain-block lookup arm.
* `RMCAbs.lean` — `abs_reset`'s cheap fields: `cycle`, `mem`, `mover`,
  `inflight`, and all four gates. `absDom_reset`, `abs_reset`, and
  `coupled_reset` are now assembled below without sorries.

## Remaining work (the sorries), itemized

1. `square` — the big one. Phase decomposition mirroring `Step.step`:
   a. rule-fold characterization: `(core m).cycle σ` as the four rules'
      `Act.run` composition (later writes win);
   b. refill: `refillCondE`/`drctr` vs `cycle % P` (uses `Coupled.rctr_sync`
      and the `effBudgetE` bypass for the charge path);
   c. core, in-flight arm: countdown vs `cyclesLeft - 1`; retirement
      dispatch — per-opcode circuit vs `Isa` exec semantics (25 ops; base
      ops first, mirroring Acc8 `AR.square`'s per-op `simp` pattern, then
      the system ops of `Hw/SysOps.lean`); the `cap_revoke` arm needs the
      pointer-doubling mark-engine correctness (`rv_*` registers converge
      to the spec `marks` closure in ≤ 7 of the 22 rounds) — this forces
      an `rv`-coupling clause into `Coupled` (currently absorbed by the
      concrete-reachability hypothesis `hcr`);
   d. core, idle arm: `schedOrder` fold vs `schedule`'s max-priority fold
      (uses `WF.prio_inj`), `payerE` unrolled walk vs `MachineState.payer`,
      fetch/decode/charge/latch vs the spec issue path;
   e. mover: `SysOps.moverAct`'s pre-cycle re-derivations vs
      `moverPhase ∘ corePhase` (kill sweeps, same-cycle store forwarding);
   f. tick: `cycle + 1`, `BitVec` addition on both sides (wraps identically).
2. `coupled_step` — preservation of `Coupled`: `rctr` increment vs counter
   increment mod `P`, canonical writes (every kind word the circuits write
   is an encoder image), `run` writes ∈ {0,1,2}.

`Coupled` is expected to grow proof-forced clauses (repo pattern); `square`
and `coupled_step` also carry `hcr` (concrete reachability), so clauses
provable from reachability can be added to `Coupled` without weakening the
assembled theorems — `lockstep_coupled` threads reachability on both sides.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw

/-! ## The coupling invariant and datapath fit -/

/-- Hidden-state / canonical-encoding coupling between a core state and its
abstraction: the register file is in the image of the encoding discipline
`Hw/Enc.lean` fixes, and the hidden refill counters track the cycle
register. (The `cap_revoke` mark-engine coupling is currently supplied by
the concrete-reachability hypothesis of `square`; it becomes a clause here
when the retirement arm forces its exact statement.) -/
structure Coupled (m : Manifest) (σ : Loom.Hw.St) : Prop where
  /-- The hidden per-domain refill counter is `cycle % P` of the *register*
  counter. The two stay in sync *through* the `2 ^ 32` wrap because
  `Manifest.WF.period_dvd` makes `P` divide `2 ^ 32`. -/
  rctr_sync : ∀ d : DomainId,
    (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP
  /-- The run state is canonically encoded (`3#2` is decode fallback only;
  the circuits test `= 0`, the spec tests `.running`). -/
  run_canon : ∀ d : DomainId, σ.regs (Hw.drun d) 2 ≠ 3#2
  /-- Every capability kind word — live or dead — is in the encoder image
  (`decKind` drops the unused high bits, which the circuits copy
  verbatim). Unconditional (dead slots keep their last canonical word;
  reset words are `0`, also canonical), so preservation never needs to
  correlate the kind register with its valid bit. -/
  kind_canon : ∀ (d : DomainId) (s : Slot),
    Hw.encKind (Hw.decKind (σ.regs (Hw.dcapKind d s) 32)) =
      σ.regs (Hw.dcapKind d s) 32
  /-- The `r0` register family (each domain's `dreg d 0` and its
  gate-saved mirror `gsreg g 0`) is pinned at zero — the spec hardwires
  architectural reads of `r0` to `0`, the circuits read the real register
  (`RMCZero`). -/
  r0_zero : R0Zero σ

/-! ## Reset -/

private theorem domainState_ext {a b : DomainState}
    (h1 : a.regs = b.regs) (h2 : a.pc = b.pc) (h3 : a.caps = b.caps)
    (h4 : a.slotGen = b.slotGen) (h5 : a.lineage = b.lineage)
    (h6 : a.regions = b.regions) (h7 : a.run = b.run)
    (h8 : a.serving = b.serving) (h9 : a.cause = b.cause)
    (h10 : a.budget = b.budget) (h11 : a.maxDonation = b.maxDonation) :
    a = b := by
  cases a; cases b; simp_all

/-- The domain blocks decode to the boot domain states. The generated
lookup arms in `RMCResetDom.lean` expose each reset register, and this proof
assembles the fields with the `RMCEnc` round trips; `budget`/`maxDonation`
use `hwf.budget_le` and `hfit` to remove the `BitVec.toNat` mod. -/
theorem absDom_reset (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (d : DomainId) :
    Hw.absDom (Hw.core m).reset d = m.initState.doms d := by
  apply domainState_ext
  · funext r
    simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_dreg]
  · simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_dpc]
  · funext s
    cases hcap : (m.doms d).initCaps s <;>
      simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_dcapV,
        reset_dcapKind, reset_dcapLinV, decKind_encKind, hcap]
  · funext s
    simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_dgen]
  · funext l
    simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_dcellV]
  · funext r
    cases hreg : (m.doms d).initRegions r with
    | none =>
        simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_drgnV,
          reset_drgn, hreg]
    | some s =>
        cases hcap : (m.doms d).initCaps s with
        | none =>
            simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_drgnV,
              reset_drgn, hreg, hcap]
        | some k =>
            cases k <;>
              simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_drgnV,
                reset_drgn, decRegion_encRegion, hreg, hcap]
  · simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_drun,
      reset_drunG, decRun_encRun]
  · simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_dsrvV]
  · simp [Hw.absDom, Manifest.initState, Manifest.bootDom, reset_dcause]
  · simp only [Hw.absDom, reset_dbudget, Manifest.initState, Manifest.bootDom]
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt
      (Nat.lt_of_le_of_lt (hwf.budget_le d) (hfit.period_lt d))
  · simp only [Hw.absDom, reset_dmaxdon, Manifest.initState, Manifest.bootDom]
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (hfit.maxdon_lt d)

private theorem machineState_ext {a b : MachineState}
    (h1 : a.cycle = b.cycle) (h2 : a.mem = b.mem) (h3 : a.doms = b.doms)
    (h4 : a.gates = b.gates) (h5 : a.mover = b.mover)
    (h6 : a.inflight = b.inflight) : a = b := by
  cases a; cases b; simp_all

/-- Reset abstracts to boot: decoding the declared reset values recovers
`m.initState` field by field. -/
theorem abs_reset (m : Manifest) (hwf : m.WF) (hfit : Fits m) :
    Hw.abs (Hw.core m).reset = m.initState :=
  machineState_ext (abs_cycle_reset m) (abs_mem_reset m)
    (funext (absDom_reset m hwf hfit)) (funext (absGate_reset m))
    (abs_mover_reset m) (abs_inflight_reset m)

/-- The coupling holds at reset (`cycle = 0`, `rctr = 0 % P`, all encodings
canonical by construction). -/
theorem coupled_reset (m : Manifest) : Coupled m (Hw.core m).reset := by
  refine ⟨?_, ?_, ?_, reset_r0_zero m⟩
  · intro d
    simp [reset_drctr, reset_cycle, Manifest.initState]
  · intro d
    simp [reset_drun, Manifest.initState, Manifest.bootDom, Hw.encRun]
  · intro d s
    cases hcap : (m.initState.doms d).caps s with
    | none =>
        rw [reset_dcapKind]
        simp only [hcap, Option.map_none, Option.getD_none]
        decide
    | some c =>
        simp [reset_dcapKind, hcap, decKind_encKind]

/-! ## The commuting square and coupling preservation -/

/-- The `cap_dup` retirement arm — remaining (NEXTSTEPS §1). -/
theorem square_retire_capdup (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 16#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The `cap_drop` retirement arm — remaining (NEXTSTEPS §1). -/
theorem square_retire_capdrop (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 17#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The `cap_revoke` retirement arm — remaining (NEXTSTEPS §1). -/
theorem square_retire_caprevoke (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The `mem_grant` retirement arm — remaining (NEXTSTEPS §1). -/
theorem square_retire_memgrant (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 19#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The `map` retirement arm — remaining (NEXTSTEPS §1). -/
theorem square_retire_map (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 20#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The `gate_call` retirement arm — remaining (NEXTSTEPS §1). -/
theorem square_retire_gatecall (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The `gate_return` retirement arm — remaining (NEXTSTEPS §1). -/
theorem square_retire_gatereturn (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The `move` retirement arm — remaining (NEXTSTEPS §1). -/
theorem square_retire_move (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 24#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  sorry

/-- The retirement arm, dispatched over the latched opcode. Sixteen op
arms plus the decode-failure fallback are proven; the nine remaining
system-op arms are the leaf obligations above (NEXTSTEPS §1). -/
theorem square_retire (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  have hsync := hcpl.rctr_sync
  have hz := hcpl.r0_zero
  by_cases h0 : (σ.regs "if_word" 32).extractLsb' 0 6 = 0#6
  · exact square_retire_add m hwf hfit σ hsync hz hifv hcl h0
  by_cases h1 : (σ.regs "if_word" 32).extractLsb' 0 6 = 1#6
  · exact square_retire_sub m hwf hfit σ hsync hz hifv hcl h1
  by_cases h2 : (σ.regs "if_word" 32).extractLsb' 0 6 = 2#6
  · exact square_retire_and m hwf hfit σ hsync hz hifv hcl h2
  by_cases h3 : (σ.regs "if_word" 32).extractLsb' 0 6 = 3#6
  · exact square_retire_or m hwf hfit σ hsync hz hifv hcl h3
  by_cases h4 : (σ.regs "if_word" 32).extractLsb' 0 6 = 4#6
  · exact square_retire_xor m hwf hfit σ hsync hz hifv hcl h4
  by_cases h5 : (σ.regs "if_word" 32).extractLsb' 0 6 = 5#6
  · exact square_retire_shl m hwf hfit σ hsync hz hifv hcl h5
  by_cases h6 : (σ.regs "if_word" 32).extractLsb' 0 6 = 6#6
  · exact square_retire_shr m hwf hfit σ hsync hz hifv hcl h6
  by_cases h7 : (σ.regs "if_word" 32).extractLsb' 0 6 = 7#6
  · exact square_retire_addi m hwf hfit σ hsync hz hifv hcl h7
  by_cases h8 : (σ.regs "if_word" 32).extractLsb' 0 6 = 8#6
  · exact square_retire_lui m hwf hfit σ hsync hz hifv hcl h8
  by_cases h9 : (σ.regs "if_word" 32).extractLsb' 0 6 = 9#6
  · exact square_retire_lw m hwf hfit σ hsync hz hifv hcl h9
  by_cases h10 : (σ.regs "if_word" 32).extractLsb' 0 6 = 10#6
  · exact square_retire_sw m hwf hfit σ hsync hz hifv hcl h10
  by_cases h11 : (σ.regs "if_word" 32).extractLsb' 0 6 = 11#6
  · exact square_retire_beq m hwf hfit σ hsync hz hifv hcl h11
  by_cases h12 : (σ.regs "if_word" 32).extractLsb' 0 6 = 12#6
  · exact square_retire_blt m hwf hfit σ hsync hz hifv hcl h12
  by_cases h13 : (σ.regs "if_word" 32).extractLsb' 0 6 = 13#6
  · exact square_retire_jalr m hwf hfit σ hsync hz hifv hcl h13
  by_cases h16 : (σ.regs "if_word" 32).extractLsb' 0 6 = 16#6
  · exact square_retire_capdup m hwf hfit σ hcpl hcr hsr hifv hcl h16
  by_cases h17 : (σ.regs "if_word" 32).extractLsb' 0 6 = 17#6
  · exact square_retire_capdrop m hwf hfit σ hcpl hcr hsr hifv hcl h17
  by_cases h18 : (σ.regs "if_word" 32).extractLsb' 0 6 = 18#6
  · exact square_retire_caprevoke m hwf hfit σ hcpl hcr hsr hifv hcl h18
  by_cases h19 : (σ.regs "if_word" 32).extractLsb' 0 6 = 19#6
  · exact square_retire_memgrant m hwf hfit σ hcpl hcr hsr hifv hcl h19
  by_cases h20 : (σ.regs "if_word" 32).extractLsb' 0 6 = 20#6
  · exact square_retire_map m hwf hfit σ hcpl hcr hsr hifv hcl h20
  by_cases h21 : (σ.regs "if_word" 32).extractLsb' 0 6 = 21#6
  · exact square_retire_unmap m hwf hfit σ hsync hz hifv hcl h21
  by_cases h22 : (σ.regs "if_word" 32).extractLsb' 0 6 = 22#6
  · exact square_retire_gatecall m hwf hfit σ hcpl hcr hsr hifv hcl h22
  by_cases h23 : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6
  · exact square_retire_gatereturn m hwf hfit σ hcpl hcr hsr hifv hcl h23
  by_cases h24 : (σ.regs "if_word" 32).extractLsb' 0 6 = 24#6
  · exact square_retire_move m hwf hfit σ hcpl hcr hsr hifv hcl h24
  by_cases h25 : (σ.regs "if_word" 32).extractLsb' 0 6 = 25#6
  · exact square_retire_yield m hwf hfit σ hsync hifv hcl h25
  by_cases h26 : (σ.regs "if_word" 32).extractLsb' 0 6 = 26#6
  · exact square_retire_halt m hwf hfit σ hsync hifv hcl h26
  -- unknown opcode: both sides fault with illegal-instruction
  refine square_retire_illegal m hwf hfit σ hsync hifv hcl ?_
  rw [decode_none_iff σ Hw.opcE (σ.regs "if_word" 32) rfl]
  intro hkn
  obtain ⟨d, hd, hop⟩ := (knownE_eval σ Hw.opcE).mp hkn
  have hmemop : d.opcode ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] : List (BitVec 6)) :=
    (by decide +kernel : ∀ d' ∈ isa, d'.opcode ∈
      ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] : List (BitVec 6)))
      d hd
  have hke : (σ.regs "if_word" 32).extractLsb' 0 6 ∈
      ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26] : List (BitVec 6)) := by
    rw [show (σ.regs "if_word" 32).extractLsb' 0 6 = d.opcode from
      hop.symm]
    exact hmemop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hke
  rcases hke with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact h0 h
  · exact h1 h
  · exact h2 h
  · exact h3 h
  · exact h4 h
  · exact h5 h
  · exact h6 h
  · exact h7 h
  · exact h8 h
  · exact h9 h
  · exact h10 h
  · exact h11 h
  · exact h12 h
  · exact h13 h
  · exact h16 h
  · exact h17 h
  · exact h18 h
  · exact h19 h
  · exact h20 h
  · exact h21 h
  · exact h22 h
  · exact h23 h
  · exact h24 h
  · exact h25 h
  · exact h26 h

/-- **The R-MC square**: one core cycle is exactly one spec step through
`Hw.abs`. Three of the four arms — countdown, idle-stall, idle-issue —
are fully proven on the bridge stack; the retirement arm
(`square_retire`) is the remaining obligation. -/
theorem square (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (hcr : ((Hw.core m).toTSys).Reachable σ)
    (hsr : (machine m).Reachable (Hw.abs σ)) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  by_cases hifv : σ.regs "if_v" 1 = 1#1
  · by_cases hcl : (σ.regs "if_cl" 8).toNat < 2
    · exact square_retire m hwf hfit σ hcpl hcr hsr hifv hcl
    · exact square_countdown m hwf hfit σ hcpl.rctr_sync hifv (by omega)
  · cases hs : schedule m (refillPhase m (Hw.abs σ)) with
    | none =>
        exact square_idle_stall m hwf hfit σ hcpl.rctr_sync hcpl.run_canon
          hifv hs
    | some e =>
        exact square_idle_issue m hwf hfit σ hcpl.rctr_sync hcpl.run_canon
          hifv e hs

/-- The kind-canonicality clause of `coupled_step`: every write any rule
makes to a `d*_cap*_kind` register is an encoder image (narrowed kinds are
packed by `encMemKindE`; installs copy other kind registers, canonical by
the unconditional invariant; everything else preserves). -/
private theorem coupled_step_kind (m : Manifest) (σ : Loom.Hw.St)
    (hcpl : Coupled m σ) (d : DomainId) (s : Slot) :
    Hw.encKind (Hw.decKind
        (((Hw.core m).cycle σ).regs (Hw.dcapKind d s) 32)) =
      ((Hw.core m).cycle σ).regs (Hw.dcapKind d s) 32 :=
  cycle_kind_canon m σ (fun c s' => hcpl.kind_canon c s') d s

/-- The coupling is preserved by one core cycle. At the wrap, `rctr` rolls
`P - 1 → 0` exactly when `cycle` rolls `2 ^ 32 - 1 → 0`, and
`(0 : Nat) % P = 0`; away from it both increment — `WF.period_dvd` is what
makes the two roll-overs coincide. -/
theorem coupled_step (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    (σ : Loom.Hw.St)
    (hcpl : Coupled m σ)
    (_hcr : ((Hw.core m).toTSys).Reachable σ)
    (_hsr : (machine m).Reachable (Hw.abs σ)) :
    Coupled m ((Hw.core m).cycle σ) := by
  refine ⟨fun d => ?_, fun d => ?_, coupled_step_kind m σ hcpl,
    cycle_r0_zero m σ hcpl.r0_zero⟩
  · -- rctr_sync: only refill writes `rctr`, only tick writes `cycle`
    rw [cycle_regs_drctr, refillAct_run_drctr, cycle_regs_cycle]
    exact rctr_step_sync (hwf.period_pos d) (hwf.period_dvd d)
      (hfit.period_lt d) _ _ (hcpl.rctr_sync d)
  · -- run_canon: every `d*_run` write is a literal 0/1/2
    exact cycle_regs_drun_ne m σ d (hcpl.run_canon d)

/-! ## Assembly (sorry-free given the square) -/

/-- `Design.run`'s successor on the right (its definition recurses on the
left). -/
private theorem design_run_succ (dz : Loom.Hw.Design) :
    ∀ (n : Nat) (σ : Loom.Hw.St),
      dz.run (n + 1) σ = dz.cycle (dz.run n σ) := by
  intro n
  induction n with
  | zero => intro σ; rfl
  | succ k ih =>
      intro σ
      show dz.run (k + 1) (dz.cycle σ) = _
      rw [ih (dz.cycle σ)]
      rfl

/-- Spec states along the run from boot are reachable. -/
theorem machine_reachable_stepN (m : Manifest) (n : Nat) :
    (machine m).Reachable (stepN m n m.initState) := by
  induction n with
  | zero => exact .init rfl
  | succ k ih =>
      rw [Wip.stepN_succ]
      exact .step ih rfl

/-- Core states along the run from reset are reachable. -/
theorem core_reachable_run (m : Manifest) (n : Nat) :
    ((Hw.core m).toTSys).Reachable ((Hw.core m).run n (Hw.core m).reset) := by
  induction n with
  | zero => exact .init rfl
  | succ k ih =>
      rw [design_run_succ]
      exact .step ih rfl

/-- The lockstep induction: abstraction equality and coupling, jointly —
for **every** `n`, no horizon. -/
theorem lockstep_coupled (m : Manifest) (hwf : m.WF) (hfit : Fits m) :
    ∀ n : Nat,
      Hw.abs ((Hw.core m).run n (Hw.core m).reset) = stepN m n m.initState ∧
      Coupled m ((Hw.core m).run n (Hw.core m).reset) := by
  intro n
  induction n with
  | zero => exact ⟨abs_reset m hwf hfit, coupled_reset m⟩
  | succ k ih =>
      obtain ⟨habs, hcpl⟩ := ih
      have hcr := core_reachable_run m k
      have hsr : (machine m).Reachable
          (Hw.abs ((Hw.core m).run k (Hw.core m).reset)) := by
        rw [habs]; exact machine_reachable_stepN m k
      refine ⟨?_, ?_⟩
      · rw [design_run_succ, square m hwf hfit _ hcpl hcr hsr, habs,
          Wip.stepN_succ]
      · rw [design_run_succ]
        exact coupled_step m hwf hfit _ hcpl hcr hsr

/-- **R-MC.** Exact whole-state lockstep, **unbounded**: after any `n`
cycles from reset — through any number of counter wraps — decoding the
core's register file yields precisely the ISS state after `n` steps from
boot. (The formal generalization of the `Tests/Lnp64uCore.lean` lockstep
runs; horizon-free since the 2026-07-04 `BitVec 32` cycle decision.) -/
theorem abs_run (m : Manifest) (hwf : m.WF) (hfit : Fits m) (n : Nat) :
    Hw.abs ((Hw.core m).run n (Hw.core m).reset) = stepN m n m.initState :=
  (lockstep_coupled m hwf hfit n).1

/-- **R-MC transport.** Every ISS invariant — in particular each of T2–T9's
invariant forms — holds of the abstraction of every core state, at every
cycle count. This is the theorem that carries the ledger onto the emitted
Verilog. -/
theorem invariant_transport (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    {P : MachineState → Prop} (hP : (machine m).Invariant P)
    (n : Nat) :
    P (Hw.abs ((Hw.core m).run n (Hw.core m).reset)) := by
  rw [abs_run m hwf hfit n]
  exact hP _ (machine_reachable_stepN m n)

/-! ## The unbounded simulation -/

/-- Reachability in a deterministic single-init system is membership in an
indexed run: the generic engine behind `core_reachable_iff` (stated over an
abstract `M` so the `Reachable` recursor applies cleanly). -/
private theorem reachable_index {M : Loom.TSys} {σ : M.S} (h : M.Reachable σ)
    (r : Nat → M.S) (hr0 : ∀ σ₀, M.init σ₀ → σ₀ = r 0)
    (hrs : ∀ a b n, M.step a b → a = r n → b = r (n + 1)) :
    ∃ n, σ = r n := by
  induction h with
  | init h0 => exact ⟨0, hr0 _ h0⟩
  | step _ hs ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, hrs _ _ n hs hn⟩

/-- Concrete reachability is exactly the boot orbit: the core is
deterministic with the single initial state `reset`. -/
theorem core_reachable_iff (m : Manifest) (σ : Loom.Hw.St) :
    ((Hw.core m).toTSys).Reachable σ ↔
      ∃ n, (Hw.core m).run n (Hw.core m).reset = σ := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := reachable_index h (fun n => (Hw.core m).run n (Hw.core m).reset)
      (fun σ₀ h0 => h0) (fun a b n hs ha => by
        have ha' : a = (Hw.core m).run n (Hw.core m).reset := ha
        show b = (Hw.core m).run (n + 1) (Hw.core m).reset
        rw [design_run_succ, ← ha']; exact hs.symm)
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    exact core_reachable_run m n

/-- The core **on its boot orbit**: same state space, same reset, the step
exercised from reachable states — every state the powered-on device ever
occupies. Its reachable set coincides with `(core m).toTSys`'s
(`reachCore_reachable_iff`), so invariants proved against it are invariants
of the full core. See the module docstring for why the unbounded simulation
lives here and not on arbitrary (garbage) register files. -/
def reachCore (m : Manifest) : Loom.TSys where
  S := Loom.Hw.St
  init := fun σ => σ = (Hw.core m).reset
  step := fun σ σ' =>
    ((Hw.core m).toTSys).Reachable σ ∧ (Hw.core m).cycle σ = σ'

/-- The boot orbit is `reachCore`-reachable. -/
theorem reachCore_reachable_run (m : Manifest) (n : Nat) :
    (reachCore m).Reachable ((Hw.core m).run n (Hw.core m).reset) := by
  induction n with
  | zero => exact .init rfl
  | succ k ih =>
      rw [design_run_succ]
      exact .step ih ⟨core_reachable_run m k, rfl⟩

/-- `reachCore` and the full core system reach exactly the same states. -/
theorem reachCore_reachable_iff (m : Manifest) (σ : Loom.Hw.St) :
    (reachCore m).Reachable σ ↔ ((Hw.core m).toTSys).Reachable σ := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := reachable_index h (fun n => (Hw.core m).run n (Hw.core m).reset)
      (fun σ₀ h0 => h0) (fun a b n hs ha => by
        have ha' : a = (Hw.core m).run n (Hw.core m).reset := ha
        show b = (Hw.core m).run (n + 1) (Hw.core m).reset
        rw [design_run_succ, ← ha']; exact hs.2.symm)
    rw [hn]
    exact core_reachable_run m n
  · intro h
    obtain ⟨n, hn⟩ := (core_reachable_iff m σ).mp h
    rw [← hn]
    exact reachCore_reachable_run m n

/-- **R-MC (the unbounded simulation).** `Hw.abs` is a genuine
`Simulation` of the ISS by the core on its boot orbit — the project plan's
`Simulation (machine m) (core.toTSys)` restricted to the states the device
can occupy. Inhabited *because* the spec counter now wraps with the
hardware's; with the `Nat` counter this type was provably empty (module
docstring). Sorry-free given `square` and the reset lemmas. -/
theorem refines (m : Manifest) (hwf : m.WF) (hfit : Fits m) :
    Nonempty (Simulation (machine m) (reachCore m)) := by
  refine ⟨{ abs := Hw.abs, init_ok := ?_, square := ?_ }⟩
  · intro σ hσ
    show Hw.abs σ = m.initState
    rw [show σ = (Hw.core m).reset from hσ]
    exact abs_reset m hwf hfit
  · rintro σ σ' ⟨hr, rfl⟩
    obtain ⟨n, rfl⟩ := (core_reachable_iff m σ).mp hr
    show step m _ = _
    rw [← design_run_succ, abs_run m hwf hfit, abs_run m hwf hfit,
      Wip.stepN_succ]

/-- Invariant pullback along the unbounded simulation, restated on the
full core system: any spec invariant holds of the abstraction of every
reachable core state. -/
theorem invariant_pullback (m : Manifest) (hwf : m.WF) (hfit : Fits m)
    {P : MachineState → Prop} (hP : (machine m).Invariant P) :
    ((Hw.core m).toTSys).Invariant (fun σ => P (Hw.abs σ)) := by
  intro σ hσ
  obtain ⟨n, rfl⟩ := (core_reachable_iff m σ).mp hσ
  rw [abs_run m hwf hfit n]
  exact hP _ (machine_reachable_stepN m n)

end Machines.Lnp64u.Theorems.RMC
