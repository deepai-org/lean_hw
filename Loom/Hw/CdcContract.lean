-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics

/-!
# D21 — the CDC contract: a verified toggle synchronizer (L3)

The board wrappers (`fpga/zc702/lnp64mini_soc_top.v`,
`lnp64mini_dual_top.v`) hold the only multi-clock logic in the stack: the
JTAG `UPDATE` domain latches a command word, flips a toggle, and a
three-flop `sysclk` chain (`t0 → t1 → t2`) turns that toggle into the
one-cycle `cmd_valid` pulse the Loom-emitted design consumes as a D15
input port.  Everything below that pulse is single-clock and already
proved; the crossing itself was prose.  D21 makes it a theorem.

**What is *not* verified.**  We do not verify physics.  The single
physical assumption is the standard MTBF one: a first-stage flop that
samples a signal inside its aperture may resolve to *either* value, but
it resolves to *some* Boolean value before the next edge, so the second
and third stages see a settled bit.  In this file that assumption is
structural: the first flop's sample on an event cycle is supplied by an
adversarial oracle `res : Nat → Bool`, and every theorem is proved for
**all** oracles.  Nothing else about timing is assumed.

## The model

* `E n = true` marks the `sysclk` cycle in which the source toggle flips
  (the abstract stand-in for a JTAG `UPDATE` edge).
* `tog E` is the settled toggle: it changes value across an event cycle.
* `s0 E res` is the wrapper's `t0`.  On a *non*-event cycle it samples the
  settled toggle (deterministic).  On an event cycle — the flip is inside
  the aperture — the oracle decides whether it captured the old or the new
  value.  That is the whole metastability model.
* `s1`, `s2` are `t1`, `t2`: clean one-cycle delays (the 2FF guarantee).
* `pulse E res n = xor (s1 n) (s2 n)` is the wrapper's `t1 ^ t2`.

`Spaced k E` is the event-rate assumption: distinct events are at least
`k` cycles apart.  On the board `k` is enormous — a JTAG scan is
microseconds and `sysclk` is 40 ns, a margin of ~10² — so the theorems
are used at `k = 4`, the smallest value that makes them true.

## What is proved

`toggleSync_sound` (for all `E`, for all oracles `res`, under `Spaced 4`):

* every event produces **exactly one** pulse, at `n+2` or `n+3` — the
  sharper `pulse_at_event` says *which*: `pulse (n+2) = res n` and
  `pulse (n+3) = !res n`, so the adversary chooses the latency and
  nothing else;
* pulses are one cycle wide (`pulse_oneWide`);
* no pulse occurs without an event (`pulse_cause`) — no spurious wakeups.

`CmdPulseTrace k ιs` is the resulting *trace class*: the interface the
wrapper delivers to an open (D15) design — a quiet start, a one-wide
pulse train with spacing at least `k`, and command fields that are stable
across the pulse's setup cycle.  `toggleSync_cmdPulseTrace` proves the
wrapper's environment is in that class.

## The downstream hook (statement only)

A theorem about an open design `d` quantifies over input traces
`ιs : Nat → InEnv` (D15).  Such a theorem may *assume*
`CmdPulseTrace k ιs` instead of quantifying over arbitrary traces: that
hypothesis is exactly the boundary between wrapper physics and Lean
proofs.  Everything to its left is discharged here from the MTBF
assumption; everything to its right is ordinary single-clock reasoning
over `Design.runOpen`.  No such design-level theorem is stated in this
file — the class is the deliverable.
-/

namespace Loom.Hw.Cdc

/-! ## The toggle synchronizer model -/

/-- The settled source toggle. `E n = true` means the toggle flips in
cycle `n`, so its settled value changes between cycle `n` and `n+1`. -/
def tog (E : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => if E n then !(tog E n) else tog E n

/-- The first synchronizer flop (`t0`).

On a quiet cycle it samples the settled toggle.  On an event cycle the
flip lands inside the sampling aperture: the metastable resolution is
handed to the oracle `res`, which may deliver the old value (`tog E n`)
or the new one (`tog E (n+1)`).  By the *next* edge the source is settled
and sampling is deterministic again — that is the MTBF assumption, and it
is the only physics in the file. -/
def s0 (E res : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => if E n then (if res n then tog E (n + 1) else tog E n) else tog E n

/-- The second synchronizer flop (`t1`): a clean delay of `s0`. -/
def s1 (E res : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => s0 E res n

/-- The third flop (`t2`): a clean delay of `s1`, used only to make the
edge detector. -/
def s2 (E res : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => s1 E res n

/-- The wrapper's `cmd_valid = t1 ^ t2`. -/
def pulse (E res : Nat → Bool) (n : Nat) : Bool :=
  xor (s1 E res n) (s2 E res n)

/-- Distinct events are at least `k` cycles apart.  (Stated for `n < m`;
by symmetry this is `|n - m| ≥ k` for distinct events.) -/
def Spaced (k : Nat) (E : Nat → Bool) : Prop :=
  ∀ n m, E n = true → E m = true → n < m → n + k ≤ m

/-! ### Elementary facts -/

@[simp] theorem tog_quiet {E : Nat → Bool} {n : Nat} (h : E n = false) :
    tog E (n + 1) = tog E n := by
  simp [tog, h]

theorem tog_event {E : Nat → Bool} {n : Nat} (h : E n = true) :
    tog E (n + 1) = !(tog E n) := by
  simp [tog, h]

theorem s0_quiet {E res : Nat → Bool} {n : Nat} (h : E n = false) :
    s0 E res (n + 1) = tog E (n + 1) := by
  simp [s0, h]

@[simp] theorem pulse_zero (E res : Nat → Bool) : pulse E res 0 = false := rfl

@[simp] theorem pulse_one (E res : Nat → Bool) : pulse E res 1 = false := rfl

/-- The edge detector, unfolded: a pulse two cycles after `n` is exactly a
change of the first flop between `n` and `n+1`. -/
theorem pulse_succ_succ (E res : Nat → Bool) (n : Nat) :
    pulse E res (n + 2) = xor (s0 E res (n + 1)) (s0 E res n) := rfl

/-- Under `Spaced k` with `1 < k`, no event sits `j` cycles after an
event, for `0 < j < k`. -/
theorem no_event_after {E : Nat → Bool} {k n j : Nat} (hs : Spaced k E)
    (hn : E n = true) (hj : 0 < j) (hjk : j < k) : E (n + j) = false := by
  cases hc : E (n + j) with
  | false => rfl
  | true => exact absurd (hs n (n + j) hn hc (by omega)) (by omega)

/-- Symmetrically: no event sits `j` cycles *before* an event. -/
theorem no_event_before {E : Nat → Bool} {k n j : Nat} (hs : Spaced k E)
    (hn : E n = true) (hj : 0 < j) (hjk : j < k) (hjn : j ≤ n) :
    E (n - j) = false := by
  cases hc : E (n - j) with
  | false => rfl
  | true => exact absurd (hs (n - j) n hc hn (by omega)) (by omega)

/-- At an event cycle the first flop is settled: the previous cycle was
quiet (spacing), so nothing was in flight. -/
theorem s0_at_event {E res : Nat → Bool} {k n : Nat} (hs : Spaced k E)
    (hk : 1 < k) (hn : E n = true) : s0 E res n = tog E n := by
  cases n with
  | zero => rfl
  | succ m =>
      have hm : E m = false := by
        have := no_event_before (k := k) (j := 1) hs hn (by omega) hk (by omega)
        simpa using this
      exact s0_quiet hm

/-! ### (a) Every event yields exactly one pulse, at `n+2` or `n+3` -/

/-- The sharp form: the adversarial resolution chooses the *latency* of
the pulse and nothing else.  `res n = true` (the first flop caught the new
value) puts the pulse at `n+2`; `res n = false` puts it at `n+3`. -/
theorem pulse_at_event {E res : Nat → Bool} {k n : Nat} (hs : Spaced k E)
    (hk : 4 ≤ k) (hn : E n = true) :
    pulse E res (n + 2) = res n ∧ pulse E res (n + 3) = !res n := by
  have h1 : E (n + 1) = false := no_event_after (k := k) hs hn (by omega) (by omega)
  have hs0n : s0 E res n = tog E n := s0_at_event (k := k) hs (by omega) hn
  have hs0n1 : s0 E res (n + 1) = if res n then !(tog E n) else tog E n := by
    simp [s0, hn, tog_event hn]
  have hs0n2 : s0 E res (n + 2) = !(tog E n) := by
    rw [s0_quiet h1, tog_quiet h1, tog_event hn]
  constructor
  · rw [pulse_succ_succ, hs0n, hs0n1]
    cases res n <;> cases tog E n <;> rfl
  · have : pulse E res (n + 3) = xor (s0 E res (n + 2)) (s0 E res (n + 1)) :=
      pulse_succ_succ E res (n + 1)
    rw [this, hs0n2, hs0n1]
    cases res n <;> cases tog E n <;> rfl

/-- Spec form of clause (a): exactly one pulse, at `n+2` or `n+3`. -/
theorem pulse_exactly_one {E res : Nat → Bool} {k n : Nat} (hs : Spaced k E)
    (hk : 4 ≤ k) (hn : E n = true) :
    (pulse E res (n + 2) = true ∧ pulse E res (n + 3) = false) ∨
    (pulse E res (n + 2) = false ∧ pulse E res (n + 3) = true) := by
  obtain ⟨h2, h3⟩ := pulse_at_event (k := k) (res := res) hs hk hn
  cases hr : res n <;> rw [hr] at h2 h3 <;>
    simp only [Bool.not_false, Bool.not_true] at h3
  · exact Or.inr ⟨h2, h3⟩
  · exact Or.inl ⟨h2, h3⟩

/-! ### (c) No pulse without an event -/

/-- Every pulse is caused by an event, two or three cycles earlier.  No
spacing assumption is needed: spurious pulses are impossible outright. -/
theorem pulse_cause {E res : Nat → Bool} {m : Nat} (hp : pulse E res m = true) :
    ∃ n, E n = true ∧ (m = n + 2 ∨ m = n + 3) := by
  match m with
  | 0 => simp at hp
  | 1 => simp at hp
  | (j + 2) =>
    rw [pulse_succ_succ] at hp
    by_cases hE : E j = true
    · exact ⟨j, hE, Or.inl rfl⟩
    · have hEf : E j = false := by revert hE; cases E j <;> simp
      have hj1 : s0 E res (j + 1) = tog E j := by
        rw [s0_quiet hEf, tog_quiet hEf]
      match j with
      | 0 => rw [hj1] at hp; simp [s0, tog] at hp
      | (i + 1) =>
        by_cases hI : E i = true
        · exact ⟨i, hI, Or.inr (by omega)⟩
        · have hIf : E i = false := by revert hI; cases E i <;> simp
          have : s0 E res (i + 1) = tog E (i + 1) := s0_quiet hIf
          rw [hj1, this] at hp
          simp at hp

/-! ### (b) Pulses are one cycle wide -/

theorem pulse_oneWide {E res : Nat → Bool} {k m : Nat} (hs : Spaced k E)
    (hk : 4 ≤ k) (hp : pulse E res m = true) : pulse E res (m + 1) = false := by
  obtain ⟨n, hn, hm⟩ := pulse_cause hp
  obtain ⟨h2, h3⟩ := pulse_at_event (k := k) (res := res) hs hk hn
  rcases hm with rfl | rfl
  · rw [h2] at hp
    simp [h3, hp]
  · -- the pulse already took the late slot; the chain is flat afterwards
    have h1 : E (n + 1) = false := no_event_after (k := k) hs hn (by omega) (by omega)
    have hc : E (n + 2) = false := no_event_after (k := k) hs hn (by omega) (by omega)
    have e2 : s0 E res (n + 2) = tog E (n + 2) := s0_quiet h1
    have e3 : s0 E res (n + 3) = tog E (n + 3) := s0_quiet hc
    have hq : tog E (n + 3) = tog E (n + 2) := tog_quiet hc
    have hp4 : pulse E res (n + 4) = xor (s0 E res (n + 3)) (s0 E res (n + 2)) :=
      pulse_succ_succ E res (n + 2)
    rw [show n + 3 + 1 = n + 4 from rfl, hp4, e2, e3, hq]
    cases tog E (n + 2) <;> rfl

/-- **D21 clause set.**  For every event stream and *every* adversarial
resolution of first-flop metastability, an event stream whose events are
at least four `sysclk` cycles apart is turned by the wrapper's
toggle/2FF/XOR structure into: exactly one pulse per event, at `n+2` or
`n+3`; pulses one cycle wide; and no pulse without an event. -/
theorem toggleSync_sound (E res : Nat → Bool) (hs : Spaced 4 E) :
    (∀ n, E n = true →
      (pulse E res (n + 2) = true ∧ pulse E res (n + 3) = false) ∨
      (pulse E res (n + 2) = false ∧ pulse E res (n + 3) = true)) ∧
    (∀ m, pulse E res m = true → pulse E res (m + 1) = false) ∧
    (∀ m, pulse E res m = true → ∃ n, E n = true ∧ (m = n + 2 ∨ m = n + 3)) :=
  ⟨fun _ hn => pulse_exactly_one (k := 4) hs (by omega) hn,
   fun _ hp => pulse_oneWide (k := 4) hs (by omega) hp,
   fun _ hp => pulse_cause hp⟩

/-! ## The trace class delivered to an open (D15) design -/

open Loom.Hw

/-- The `cmd_valid` pin as a Boolean, read at the design's declared width. -/
def cmdValidB (ιs : Nat → InEnv) (n : Nat) : Bool := ιs n "cmd_valid" 1 != 0#1

/-- The `cmd_idx` pin at its declared width. -/
def cmdIdxV (ιs : Nat → InEnv) (n : Nat) : BitVec 7 := ιs n "cmd_idx" 7

/-- The `cmd_data` pin at its declared width. -/
def cmdDataV (ιs : Nat → InEnv) (n : Nat) : BitVec 32 := ιs n "cmd_data" 32

/-- **The wrapper/design interface.**  An input trace is a *command pulse
trace with spacing `k`* when

* `quiet`: the first two cycles carry no pulse (the synchronizer is
  flushing);
* `oneWide`: a pulse is never immediately followed by another;
* `spaced`: distinct pulses are at least `k` cycles apart;
* `idxStable` / `dataStable`: the command fields already carry their final
  value in the pulse's *setup* cycle, so a design that samples them at the
  pulse edge — or one cycle of pipelining before it — sees one settled
  value.

A design-level theorem over `Design.runOpen d ιs` may assume this class;
`toggleSync_cmdPulseTrace` discharges it from the metastability model. -/
structure CmdPulseTrace (k : Nat) (ιs : Nat → InEnv) : Prop where
  quiet : ∀ n, n < 2 → cmdValidB ιs n = false
  oneWide : ∀ n, cmdValidB ιs n = true → cmdValidB ιs (n + 1) = false
  spaced : ∀ n m, cmdValidB ιs n = true → cmdValidB ιs m = true → n < m → n + k ≤ m
  idxStable : ∀ n, cmdValidB ιs (n + 1) = true → cmdIdxV ιs n = cmdIdxV ιs (n + 1)
  dataStable : ∀ n, cmdValidB ιs (n + 1) = true → cmdDataV ιs n = cmdDataV ιs (n + 1)

/-- Spacing is monotone: a trace that is `k`-spaced is `j`-spaced for any
`j ≤ k`. -/
theorem CmdPulseTrace.mono {j k : Nat} {ιs : Nat → InEnv} (hjk : j ≤ k)
    (h : CmdPulseTrace k ιs) : CmdPulseTrace j ιs :=
  { h with spaced := fun n m hn hm hlt => by have := h.spaced n m hn hm hlt; omega }

/-- A latched command field: it changes only across an event cycle — the
`UPDATE` edge that flips the toggle is the same edge that loads
`lat_idx`/`lat_dat`, and nothing else writes them. -/
def FieldsLatched {α : Type} (E : Nat → Bool) (f : Nat → α) : Prop :=
  ∀ n, E n = false → f (n + 1) = f n

/-- The input trace the wrapper drives: `cmd_valid` is the synchronizer's
pulse, `cmd_idx`/`cmd_data` are the latched fields, every other pin is
zero. -/
def cmdEnv (E res : Nat → Bool) (idx : Nat → BitVec 7) (dat : Nat → BitVec 32) :
    Nat → InEnv := fun n nm w =>
  if nm = "cmd_valid" then (BitVec.ofBool (pulse E res n)).setWidth w
  else if nm = "cmd_idx" then (idx n).setWidth w
  else if nm = "cmd_data" then (dat n).setWidth w
  else 0#w

@[simp] theorem cmdValidB_cmdEnv (E res : Nat → Bool) (idx : Nat → BitVec 7)
    (dat : Nat → BitVec 32) (n : Nat) :
    cmdValidB (cmdEnv E res idx dat) n = pulse E res n := by
  cases h : pulse E res n <;> simp [cmdValidB, cmdEnv, h]

@[simp] theorem cmdIdxV_cmdEnv (E res : Nat → Bool) (idx : Nat → BitVec 7)
    (dat : Nat → BitVec 32) (n : Nat) :
    cmdIdxV (cmdEnv E res idx dat) n = idx n := by
  simp [cmdIdxV, cmdEnv]

@[simp] theorem cmdDataV_cmdEnv (E res : Nat → Bool) (idx : Nat → BitVec 7)
    (dat : Nat → BitVec 32) (n : Nat) :
    cmdDataV (cmdEnv E res idx dat) n = dat n := by
  simp [cmdDataV, cmdEnv]

/-- The cycle before a pulse is quiet: a pulse at `n+1` comes from an
event at `n-1` or `n-2`, and spacing keeps `E n` low. -/
theorem no_event_before_pulse {E res : Nat → Bool} {k n : Nat} (hs : Spaced k E)
    (hk : 4 ≤ k) (hp : pulse E res (n + 1) = true) : E n = false := by
  obtain ⟨e, he, hm⟩ := pulse_cause hp
  rcases hm with h | h
  · have : n = e + 1 := by omega
    subst this
    exact no_event_after (k := k) hs he (by omega) (by omega)
  · have : n = e + 2 := by omega
    subst this
    exact no_event_after (k := k) hs he (by omega) (by omega)

/-- Two pulses arising from the same event are the same pulse. -/
theorem pulse_same_event {E res : Nat → Bool} {k n : Nat} (hs : Spaced k E)
    (hk : 4 ≤ k) (hn : E n = true) (h2 : pulse E res (n + 2) = true)
    (h3 : pulse E res (n + 3) = true) : False := by
  obtain ⟨e2, e3⟩ := pulse_at_event (k := k) (res := res) hs hk hn
  rw [h2] at e2
  rw [h3] at e3
  rw [← e2] at e3
  simp at e3

/-- **The composition theorem.**  Feed the verified toggle synchronizer
and the latched command fields to an open design: the resulting input
trace is a `CmdPulseTrace`, for every adversarial resolution.  Events
`k` cycles apart (`k ≥ 4`) give pulses at least `k - 1` cycles apart. -/
theorem toggleSync_cmdPulseTrace {k : Nat} (E res : Nat → Bool)
    (idx : Nat → BitVec 7) (dat : Nat → BitVec 32)
    (hs : Spaced k E) (hk : 4 ≤ k)
    (hidx : FieldsLatched E idx) (hdat : FieldsLatched E dat) :
    CmdPulseTrace (k - 1) (cmdEnv E res idx dat) where
  quiet n hn := by
    match n with
    | 0 => simp
    | 1 => simp
    | (j + 2) => exact absurd hn (by omega)
  oneWide n hn := by
    simp only [cmdValidB_cmdEnv] at hn ⊢
    exact pulse_oneWide (k := k) hs hk hn
  spaced n m hn hm hlt := by
    simp only [cmdValidB_cmdEnv] at hn hm
    obtain ⟨a, ha, hna⟩ := pulse_cause hn
    obtain ⟨b, hb, hmb⟩ := pulse_cause hm
    have hab : a ≠ b := by
      rintro rfl
      -- one event cannot produce two pulses
      have hn2 : n = a + 2 := by rcases hna with h | h <;> rcases hmb with h' | h' <;> omega
      have hm3 : m = a + 3 := by rcases hna with h | h <;> rcases hmb with h' | h' <;> omega
      subst hn2; subst hm3
      exact pulse_same_event (k := k) hs hk ha hn hm
    have hlt' : a < b := by
      rcases Nat.lt_trichotomy a b with h | h | h
      · exact h
      · exact absurd h hab
      · have := hs b a hb ha h
        omega
    have hab' := hs a b ha hb hlt'
    rcases hna with rfl | rfl <;> rcases hmb with rfl | rfl <;> omega
  idxStable n hn := by
    simp only [cmdValidB_cmdEnv] at hn
    exact (hidx n (no_event_before_pulse (k := k) hs hk hn)).symm
  dataStable n hn := by
    simp only [cmdValidB_cmdEnv] at hn
    exact (hdat n (no_event_before_pulse (k := k) hs hk hn)).symm

/-- Spec-shaped corollary: spacing `k` in, `k - 3` out. -/
theorem toggleSync_cmdPulseTrace' {k : Nat} (E res : Nat → Bool)
    (idx : Nat → BitVec 7) (dat : Nat → BitVec 32)
    (hs : Spaced k E) (hk : 4 ≤ k)
    (hidx : FieldsLatched E idx) (hdat : FieldsLatched E dat) :
    CmdPulseTrace (k - 3) (cmdEnv E res idx dat) :=
  CmdPulseTrace.mono (by omega)
    (toggleSync_cmdPulseTrace E res idx dat hs hk hidx hdat)

end Loom.Hw.Cdc
