import Machines.Lnp64u.Hw.SysOps

/-!
# The LNP64-µ core in the hardware EDSL (task 1.11)

Direct implementation, 1 hardware cycle = 1 spec cycle (`Hw/DESIGN.md`).
Rules, in order (later writes win = spec phase order):

1. `refill` — period-boundary budget refill (hidden mod-counters `d{d}_rctr`
   track `cycle % periodP`, since `Expr` has no modulo).
2. `core` — in-flight countdown / retirement, else schedule → fetch →
   decode → upfront charge → latch (`Step.corePhase`). All core-phase
   memory writes (`sw` stores and the sweeps' Mover-status writes) fold
   into ONE syntactic port-0 write at the dispatch level.
3. `mover` — `Step.moverPhase` on the post-core state (`SysOps.moverAct`);
   data word on port 1, status word on port 2 — ascending port indices =
   spec phase/write order, and the design has exactly one syntactic write
   per port, so `Compile.MemWriteWF` holds.
4. `tick` — `cycle := cycle + 1`.

**Refill bypass (spec-fidelity corner).** The spec's core phase runs on the
*post-refill* state, but EDSL reads are pre-cycle (D9). So every budget the
core rule consumes goes through `effBudgetE`, which re-computes the refill
in-line; when the core charges, its (later) write to the payer's budget
wins over the refill rule's write — exactly the spec's
`refillPhase ∘ corePhase` composition.

**`cap_revoke` mark engine.** The first countdown cycle of an in-flight
`cap_revoke` initializes the hidden pointer-doubling registers
(`SysOps.rvInit`, keyed off `if_cl = revokeCost`); each further countdown
cycle runs one doubling round (`SysOps.rvStep`, 22 rounds ≥ the 7 needed);
retirement consumes the converged mark vector. See `SysOps.lean` for the
closure argument.

Module structure: `Hw/Enc.lean` (names, packings, regDecls/memDecl, `abs`),
`Hw/BaseOps.lean` (shared circuits), `Hw/SysOps.lean` (all 25 op circuits +
the Mover composite), `Hw/Core.lean` (this file: scheduler, issue, rules).
-/

namespace Machines.Lnp64u.Hw

open Loom.Hw

/-! ## Refill and the budget bypass -/

/-- Does domain `d`'s budget refill this cycle (`cycle % P = 0`, via the
hidden mod-counter)? No boot-skip conjunct: with a wrapping counter, boot
is indistinguishable from a wrap, and wrap boundaries must refill (spec
`refillPhase`, 2026-07-04). At boot the refill re-writes the reset value
`budgetQ`, a no-op. -/
def refillCondE (d : DomainId) : Expr 1 :=
  .eq (.reg 32 (drctr d)) (.lit 0)

/-- Domain `d`'s budget *as the spec's core phase sees it* (post-refill). -/
def effBudgetE (m : Manifest) (d : DomainId) : Expr 32 :=
  .mux (refillCondE d) (.lit (BitVec.ofNat 32 (m.doms d).budgetQ))
       (.reg 32 (dbudget d))

/-- Rule 1: refill budgets at period boundaries; advance the mod-counters. -/
def refillAct (m : Manifest) : Act :=
  seqAll <| (List.finRange numDomains).map fun d =>
    let ctr : Expr 32 := .reg 32 (drctr d)
    .seq
      (.ite (refillCondE d)
        (.write 32 (dbudget d) (.lit (BitVec.ofNat 32 (m.doms d).budgetQ)))
        .skip)
      (.write 32 (drctr d)
        (.mux (.eq ctr (.lit (BitVec.ofNat 32 ((m.doms d).periodP - 1))))
          (.lit 0) (.add ctr (.lit 1))))

/-! ## Scheduling: the payer walk and the static priority chain -/

/-- One step of the serving-chain walk from a *static* domain: if `c` is
serving a gate with a live activation, move to that activation's caller.
Small per static `c`, so the iterated walk below composes 4-way muxes over
these instead of substituting a growing expression into three selector
positions (which blew the emitted tree up exponentially). -/
def chainNextE (c : DomainId) : Expr 2 :=
  let g : Expr 2 := .reg 2 (dsrv c)
  .mux (.and (.reg 1 (dsrvV c)) (muxFin (fun gg => .reg 1 (gactV gg)) g))
       (muxFin (fun gg => .reg 2 (gcaller gg)) g) (dLit c)

/-- The budget payer of domain `d` (`MachineState.payer`): the
serving-chain origin, unrolled `maxChainDepth` steps (a stopped walk is a
fixpoint of the step, so iteration = fuel-bounded recursion). -/
def payerE (d : DomainId) : Expr 2 :=
  (List.range maxChainDepth).foldl
    (fun e _ => muxFin (fun c => chainNextE c) e) (dLit d)

/-- Schedule eligibility (`Step.schedule`'s filter): running, and the
payer's (post-refill) budget is nonzero. -/
def eligE (m : Manifest) (d : DomainId) : Expr 1 :=
  .and (.eq (.reg 2 (drun d)) (.lit 0))
       (.not (.eq (muxFin (fun p => effBudgetE m p) (payerE d)) (.lit 0)))

/-- Domains in scheduling order: priority descending, index ascending on
ties (= the winner of `Step.schedule`'s fold is the first eligible one). -/
def schedOrder (m : Manifest) : List DomainId :=
  (List.finRange numDomains).mergeSort fun a b =>
    (m.doms b).priority ≤ (m.doms a).priority

/-! ## Issue: fetch → decode → charge → latch -/

/-- Attempt to issue for domain `d` (`Step.corePhase`'s idle path): fetch
under execute authority, decode, upfront budget charge (payer, and the
donation draw-down when serving), latch in-flight. Fetch/decode failure is
a domain-fatal fault consuming the cycle; a short budget stalls (no
writes). -/
def issueFor (m : Manifest) (d : DomainId) : Act :=
  let pc := rPc d
  let w : Expr 32 := .memRead 32 "mem" pc
  let opc : Expr 6 := field w 0 6
  let cost8 : Expr 8 := costE opc
  let cost32 : Expr 32 := .zext cost8 32
  let p : Expr 2 := payerE d
  let effB : Expr 32 := muxFin (fun q => effBudgetE m q) p
  let charge : Act := seqAll <| (List.finRange numDomains).map fun q =>
    .ite (.eq p (.lit (BitVec.ofNat 2 q.val)))
      (.write 32 (dbudget q) (.sub (effBudgetE m q) cost32)) .skip
  let latch : Act :=
    .seq (.write 1 "if_v" (.lit 1)) <|
    .seq (.write 2 "if_dom" (.lit (BitVec.ofNat 2 d.val))) <|
    .seq (.write 32 "if_word" w) (.write 8 "if_cl" cost8)
  let gid : Expr 2 := .reg 2 (dsrv d)
  let actv : Expr 1 := muxFin (fun g => .reg 1 (gactV g)) gid
  let don : Expr 32 := muxFin (fun g => .reg 32 (gdon g)) gid
  let drawDon : Act := seqAll <| (List.finRange numGates).map fun g =>
    .ite (.eq gid (.lit (BitVec.ofNat 2 g.val)))
      (.write 32 (gdon g) (.sub don cost32)) .skip
  .ite (.not (domCoversE d pc ⟨false, false, true⟩))
    (haltFault d .memoryAuthority) <|
  .ite (.not (knownE opc)) (haltFault d .illegalInstruction) <|
  .ite (.ult effB cost32) .skip <|  -- stall until refill
  .ite (.reg 1 (dsrvV d))
    (-- serving: draw the activation's donation down as well (T6)
     .ite (.not actv) (haltFault d .protocol) <|
     .ite (.ult don cost32) (haltFault d .budget) <|
     .seq charge (.seq drawDon latch))
    (.seq charge latch)

/-! ## The core rule -/

/-- Retirement: clear in-flight, dispatch on the owning domain, and commit
the ops' single muxed port-0 memory write. -/
def retireAct : Act :=
  let (en, ad, da) := (List.finRange numDomains).foldr
    (fun d (en, ad, da) =>
      let (en_d, ad_d, da_d) := retireMemFor d
      let g := .and (ifDomIs d) en_d
      (.or g en, .mux g ad_d ad, .mux g da_d da))
    ((.lit 0 : Expr 1), (.lit 0 : Expr 12), (.lit 0 : Expr 32))
  .seq (.write 1 "if_v" (.lit 0)) <|
  .seq (seqAll <| (List.finRange numDomains).map fun d =>
      .ite (ifDomIs d) (retireFor d) .skip)
    (.ite en (.memWrite 12 32 "mem" 0 ad da) .skip)

/-- Rule 2 (`Step.corePhase`): countdown/retire when an instruction is in
flight (an in-flight `cap_revoke` runs one mark-doubling round per
countdown cycle), else try to issue for the highest-priority eligible
domain. -/
def coreAct (m : Manifest) : Act :=
  .ite (.reg 1 "if_v")
    (.ite (.ult (.reg 8 "if_cl") (.lit 2))
      retireAct
      (.seq (.write 8 "if_cl" (.sub (.reg 8 "if_cl") (.lit 1)))
        (.ite (isMn "cap_revoke")
          (.ite (.eq (.reg 8 "if_cl") (.lit (BitVec.ofNat 8 revokeCost)))
            rvInit rvStep)
          .skip)))
    ((schedOrder m).foldr (fun d acc => .ite (eligE m d) (issueFor m d) acc)
      .skip)

/-- Rule 4: the cycle counter. -/
def tickAct : Act := .write 32 "cycle" (.add (.reg 32 "cycle") (.lit 1))

/-- The LNP64-µ core for a configured machine. -/
def core (m : Manifest) : Design where
  name := "lnp64u"
  regs := regDecls m
  mems := [memDecl m]
  rules := [⟨"refill", refillAct m⟩, ⟨"core", coreAct m⟩,
            ⟨"mover", moverAct⟩, ⟨"tick", tickAct⟩]

end Machines.Lnp64u.Hw
