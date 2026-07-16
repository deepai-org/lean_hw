-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCRetireGateReturnSuccessArm

/-!
# Complete `gate_return` retirement dispatcher

This file assembles the five ordered hardware checks and the two successful
reply cases proved by the `RMCRetireGateReturn*` modules.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom Loom.Hw Machines.Lnp64u.Hw

/-- The complete `gate_return` retirement arm, dispatched in the same order as
`Hw.retChecks`: serving activation, active gate, live reply, matching class,
free destination, then null/non-null success. -/
theorem square_retire_gateReturn (m : Manifest) (hwf : m.WF)
    (hfit : Fits m) (σ : Loom.Hw.St)
    (hsync : ∀ d : DomainId, (σ.regs (Hw.drctr d) 32).toNat =
      (σ.regs "cycle" 32).toNat % (m.doms d).periodP)
    (hz : R0Zero σ) (hkc : KindCanon σ)
    (hsr : (machine m).Reachable (Hw.abs σ))
    (hifv : σ.regs "if_v" 1 = 1#1)
    (hcl : (σ.regs "if_cl" 8).toNat < 2)
    (hopc : (σ.regs "if_word" 32).extractLsb' 0 6 = 23#6) :
    Hw.abs ((Hw.core m).cycle σ) = step m (Hw.abs σ) := by
  let E : DomainId := finOfBv (by decide) (σ.regs "if_dom" 2)
  by_cases hserving : σ.regs (Hw.dsrvV E) 1 = 1#1
  · by_cases hactive : (Hw.muxFin (fun g => .reg 1 (Hw.gactV g))
        (Hw.retGid E)).eval σ = 1#1
    · let gid : GateId := finOfBv (by decide) ((Hw.retGid E).eval σ)
      have hserv : ((Hw.abs σ).doms E).serving = some gid := by
        change (if σ.regs (Hw.dsrvV E) 1 = 1#1 then
          some (finOfBv (by decide) (σ.regs (Hw.dsrv E) 2)) else none) =
            some gid
        rw [if_pos hserving]
        rfl
      have hgid := retGid_eval_selected σ E gid hserv
      have hactV : σ.regs (Hw.gactV gid) 1 = 1#1 := by
        rw [muxFin_eval (by decide : 2 ^ 2 = numGates), hgid] at hactive
        exact hactive
      let act : Activation :=
        { caller := finOfBv (by decide) (σ.regs (Hw.gcaller gid) 2)
          callerRd := finOfBv (by decide) (σ.regs (Hw.gcallerRd gid) 3)
          savedRegs := fun r => σ.regs (Hw.gsreg gid r) 32
          savedPc := σ.regs (Hw.gspc gid) 12
          savedServing :=
            if σ.regs (Hw.gssrvV gid) 1 = 1#1 then
              some (finOfBv (by decide) (σ.regs (Hw.gssrv gid) 2))
            else none
          depth := (σ.regs (Hw.gdepth gid) 3).toNat
          donated := (σ.regs (Hw.gdon gid) 32).toNat }
      have hact : ((Hw.abs σ).gates gid).act = some act := by
        show (Hw.absGate σ gid).act = some act
        change (if σ.regs (Hw.gactV gid) 1 = 1#1 then _ else none) =
          some act
        rw [if_pos hactV]
        rfl
      by_cases hstale : (Expr.and (Hw.retNZ E)
          (Expr.not (Hw.retSel E).live)).eval σ = 1#1
      · exact square_retire_gateReturn_stale m hwf hfit σ hsync hz hifv
          hcl hopc gid act (by simpa [E] using hserv)
          hact (by simpa [E] using hstale)
      · by_cases hclass : (Expr.and (Hw.retNZ E)
            (Expr.not (Hw.retSel E).clsOk)).eval σ = 1#1
        · exact square_retire_gateReturn_badClass m hwf hfit σ hsync hz hkc
            hifv hcl hopc gid act (by simpa [E] using hserv) hact
            (by simpa [E] using hstale) (by simpa [E] using hclass)
        · by_cases hblocked : (Expr.and (Hw.retNZ E)
              (Hw.transferBlocked E (Hw.retCl E) (Hw.retSel E))).eval σ = 1#1
          · exact square_retire_gateReturn_blocked m hwf hfit σ hsync hz hkc
              hsr hifv hcl hopc gid act (by simpa [E] using hserv) hact
              (by simpa [E] using hstale) (by simpa [E] using hclass)
              (by simpa [E] using hblocked)
          · by_cases hzero : (Hw.retW E).eval σ = 0#32
            · have hok : (Hw.retOkE E).eval σ = 1#1 :=
                retOkE_of_passes σ E gid act hserv hact hstale hclass hblocked
              exact square_retire_gateReturn_success_zero m hwf hfit σ hsync
                hz hsr hifv hcl hopc gid act (by simpa [E] using hserv) hact
                (by simpa [E] using hok) (by simpa [E] using hzero)
            · exact square_retire_gateReturn_success_nonzero m hwf hfit σ
                hsync hz hkc hsr hifv hcl hopc gid act
                (by simpa [E] using hserv) hact (by simpa [E] using hzero)
                (by simpa [E] using hstale) (by simpa [E] using hclass)
                (by simpa [E] using hblocked)
    · exact square_retire_gateReturn_inactive m hwf hfit σ hsync hifv hcl
        hopc (by simpa [E] using hserving) (by simpa [E] using hactive)
  · exact square_retire_gateReturn_notServing m hwf hfit σ hsync hifv hcl
      hopc (by simpa [E] using hserving)

end Machines.Lnp64u.Theorems.RMC
