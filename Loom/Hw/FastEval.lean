-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Semantics
import Loom.Hw.Notation
import Loom.Runner

/-!
# FastEval — the verified fast evaluator (L3)

`Loom/Hw/Semantics.lean` models state with closure-based environments
(`RegEnv := String → (w : Nat) → BitVec w`).  Every write extends a closure
chain, so a read after `n` writes costs `O(n)` string comparisons and
`Design.run` is quadratic in the cycle count.  That historically encouraged
machines to grow a second, hand-written ISS fast enough to be a silicon
oracle.

This module removes that limitation.  A `Design` is *elaborated once* into
an index-resolved `FastDesign` (registers and inputs → one contiguous index
space; memories → one flat array with per-memory bases; expressions → a
width-erased op tree with all indices and width constants pre-resolved),
and cycled with flat `Array Nat` state.

Representation choices and their justification live in
`Loom/Hw/FASTEVAL_SPEC.md`; the short version:

* values are `Nat`s already reduced mod `2 ^ width`, because `BitVec w` *is*
  `Fin (2 ^ w)` and core provides a `toNat` characterisation of every
  operator — which is exactly what the correctness proof induces over;
* memories are one flat array, so "a write to one memory misses another"
  is a single arithmetic disjointness lemma;
* elaboration is a plain total function: no `unsafe`, no `implemented_by`,
  no new trust surface.

The correctness statement is per coordinate (`Agree`), not extensional
equality of `St`s: `RegEnv` holds unobservable junk at undeclared
names/widths that no flat array can reproduce.  `Agree.peekReg` /
`Agree.peekMem` give the extensional consequence on declared coordinates,
which is what an oracle actually consumes.

Everything here is proved; the file's axiom closure is the classical
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Loom.Hw

/-! ## The elaborated forms -/

/-- Width-erased expressions with pre-resolved indices.  Each node carries
the numeric constants its `Nat` semantics needs (`2 ^ w`, `2 ^ w - 1`, the
sign bit `2 ^ (w-1)`, …), computed once at elaboration time. -/
inductive FExpr where
  /-- Literal, already reduced mod `2 ^ w`. -/
  | lit (v : Nat)
  /-- Register/input read at a resolved index. -/
  | reg (i : Nat)
  /-- Memory read: `base` is the memory's offset in the flat array. -/
  | memRead (base : Nat) (a : FExpr)
  | and (a b : FExpr)
  | or (a b : FExpr)
  | xor (a b : FExpr)
  /-- `mask = 2 ^ w - 1`. -/
  | not (mask : Nat) (a : FExpr)
  /-- `m = 2 ^ w`. -/
  | add (m : Nat) (a b : FExpr)
  /-- `m = 2 ^ w`. -/
  | sub (m : Nat) (a b : FExpr)
  /-- `m = 2 ^ w`. -/
  | mul (m : Nat) (a b : FExpr)
  | udiv (a b : FExpr)
  | urem (a b : FExpr)
  /-- `w` is the width (shift-amount guard), `m = 2 ^ w`. -/
  | shl (w m : Nat) (a b : FExpr)
  /-- `w` is the width (shift-amount guard). -/
  | shr (w : Nat) (a b : FExpr)
  | eq (a b : FExpr)
  | ult (a b : FExpr)
  /-- `h = 2 ^ (w - 1)`, the sign bit of the operand width. -/
  | slt (h : Nat) (a b : FExpr)
  | mux (c t f : FExpr)
  /-- `lo` is the low bit, `m = 2 ^ len`. -/
  | slice (lo m : Nat) (a : FExpr)
  /-- `m = 2 ^ w'`. -/
  | zext (m : Nat) (a : FExpr)
  /-- `h = 2 ^ (w - 1)` (source sign bit), `m = 2 ^ w'`,
  `d = 2 ^ w' - 2 ^ w` (zero when narrowing). -/
  | sext (h m d : Nat) (a : FExpr)
  deriving Inhabited, Repr, BEq, ReflBEq, DecidableEq, Hashable, LawfulBEq

/-- Width-erased actions with pre-resolved indices. -/
inductive FAct where
  | skip
  | seq (a b : FAct)
  | ite (c : FExpr) (t e : FAct)
  | write (i : Nat) (v : FExpr)
  | writeSlice (i totalWidth lo fieldWidth : Nat) (v : FExpr)
  | memWrite (base : Nat) (addr data : FExpr)
  deriving Inhabited

/-- Flat design state: registers+inputs in one array, all memories
concatenated into another.  Every entry is already reduced modulo the
width of its coordinate. -/
structure FastSt where
  regs : Array Nat
  mems : Array Nat
  deriving Inhabited

/-- The elaborated design: everything `fastCycle` touches is index-resolved.
`names` and `nregs`/`memTotal` are readback/allocation metadata only. -/
structure FastDesign where
  /-- One elaborated action per rule, in rule order. -/
  acts : Array FAct
  /-- Input ports as `(index, name, width)`, in declaration order. -/
  slots : List (Nat × String × Nat)
  nregs : Nat
  memTotal : Nat
  /-- `(name, width)` per register index — for readback, never in the loop. -/
  names : Array (String × Nat)
  deriving Inhabited

/-! ## Evaluation -/

/-- Evaluate an elaborated expression against the pre-cycle flat state. -/
def FExpr.eval (pr pm : Array Nat) : FExpr → Nat
  | .lit v => v
  | .reg i => pr.getD i 0
  | .memRead base a => pm.getD (base + a.eval pr pm) 0
  | .and a b => a.eval pr pm &&& b.eval pr pm
  | .or a b => a.eval pr pm ||| b.eval pr pm
  | .xor a b => a.eval pr pm ^^^ b.eval pr pm
  | .not mask a => mask - a.eval pr pm
  | .add m a b => (a.eval pr pm + b.eval pr pm) % m
  | .sub m a b => (m - b.eval pr pm + a.eval pr pm) % m
  | .mul m a b => (a.eval pr pm * b.eval pr pm) % m
  | .udiv a b => a.eval pr pm / b.eval pr pm
  | .urem a b => a.eval pr pm % b.eval pr pm
  | .shl w m a b =>
      let s := b.eval pr pm
      if s < w then (a.eval pr pm <<< s) % m else 0
  | .shr w a b =>
      let s := b.eval pr pm
      if s < w then a.eval pr pm >>> s else 0
  | .eq a b => if a.eval pr pm = b.eval pr pm then 1 else 0
  | .ult a b => if a.eval pr pm < b.eval pr pm then 1 else 0
  | .slt h a b =>
      let va := a.eval pr pm
      let vb := b.eval pr pm
      if ((decide (h ≤ va) != decide (h ≤ vb)).xor (decide (va < vb))) then 1 else 0
  | .mux c t f => if c.eval pr pm = 1 then t.eval pr pm else f.eval pr pm
  | .slice lo m a => (a.eval pr pm >>> lo) % m
  | .zext m a => a.eval pr pm % m
  | .sext h m d a =>
      let va := a.eval pr pm
      va % m + (if h ≤ va then d else 0)

/-- Run an elaborated action: reads from the pre-cycle arrays `pr`/`pm`,
writes onto the accumulator (last write wins — D9). -/
def FAct.run (pr pm : Array Nat) : FAct → FastSt → FastSt
  | .skip, acc => acc
  | .seq a b, acc => b.run pr pm (a.run pr pm acc)
  | .ite c t e, acc =>
      if c.eval pr pm = 1 then t.run pr pm acc else e.run pr pm acc
  | .write i v, acc =>
      { acc with regs := acc.regs.setIfInBounds i (v.eval pr pm) }
  | .writeSlice i totalWidth lo fieldWidth v, acc =>
      let next := Loom.Word.insert lo
        (BitVec.ofNat fieldWidth (v.eval pr pm))
        (BitVec.ofNat totalWidth (acc.regs.getD i 0))
      { acc with regs := acc.regs.setIfInBounds i next.toNat }
  | .memWrite base a dv, acc =>
      { acc with
        mems := acc.mems.setIfInBounds (base + a.eval pr pm) (dv.eval pr pm) }

/-- One cycle of an elaborated design. -/
def fastCycle (fd : FastDesign) (fs : FastSt) : FastSt :=
  fd.acts.foldl (fun acc a => a.run fs.regs fs.mems acc) fs

/-- Run `n` cycles (tail-recursive). -/
def fastRun (fd : FastDesign) : Nat → FastSt → FastSt
  | 0, fs => fs
  | n + 1, fs => fastRun fd n (fastCycle fd fs)

/-! ## Static elaboration context -/

/-- Registers and inputs share one index space; inputs (D15) are read with
`Expr.reg` and simply live after the registers. -/
def Design.regList (d : Design) : List (String × Nat) :=
  d.regs.map (fun r => (r.name, r.width)) ++ d.inputs.map (fun i => (i.name, i.width))

def Design.regEntry (d : Design) (i : Nat) : String × Nat :=
  d.regList.getD i ("", 0)

def Design.regIdx (d : Design) (n : String) : Option Nat :=
  d.regList.findIdx? (fun e => e.1 == n)

def Design.memIdx (d : Design) (n : String) : Option Nat :=
  d.mems.findIdx? (fun m => m.name == n)

/-- Offset of memory `k` in the flat memory array. -/
def memBaseOf : List MemDecl → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | m :: t, k + 1 => 2 ^ m.addrWidth + memBaseOf t k

def Design.memBase (d : Design) (k : Nat) : Nat := memBaseOf d.mems k

def Design.memTotal (d : Design) : Nat := memBaseOf d.mems d.mems.length

/-! ## Elaboration -/

/-- Elaborate an expression: resolve names to indices, precompute width
constants.  Total — unresolvable names elaborate to `0`, which `fastWFB`
rules out. -/
def Design.elabExpr (d : Design) : {w : Nat} → Expr w → FExpr
  | _, .lit v => .lit v.toNat
  | _, .reg _ n => match d.regIdx n with
      | some i => .reg i
      | none => .lit 0
  | _, .memRead _ m addr =>
      match d.memIdx m with
      | some k => .memRead (d.memBase k) (d.elabExpr addr)
      | none => .lit 0
  | _, .and a b => .and (d.elabExpr a) (d.elabExpr b)
  | _, .or a b => .or (d.elabExpr a) (d.elabExpr b)
  | _, .xor a b => .xor (d.elabExpr a) (d.elabExpr b)
  | w, .not a => .not (2 ^ w - 1) (d.elabExpr a)
  | w, .add a b => .add (2 ^ w) (d.elabExpr a) (d.elabExpr b)
  | w, .sub a b => .sub (2 ^ w) (d.elabExpr a) (d.elabExpr b)
  | w, .mul a b => .mul (2 ^ w) (d.elabExpr a) (d.elabExpr b)
  | _, .udiv a b => .udiv (d.elabExpr a) (d.elabExpr b)
  | _, .urem a b => .urem (d.elabExpr a) (d.elabExpr b)
  | w, .shl a b => .shl w (2 ^ w) (d.elabExpr a) (d.elabExpr b)
  | w, .shr a b => .shr w (d.elabExpr a) (d.elabExpr b)
  | _, .eq a b => .eq (d.elabExpr a) (d.elabExpr b)
  | _, .ult a b => .ult (d.elabExpr a) (d.elabExpr b)
  | _, .slt (w := sw) a b => .slt (2 ^ (sw - 1)) (d.elabExpr a) (d.elabExpr b)
  | _, .mux c t f => .mux (d.elabExpr c) (d.elabExpr t) (d.elabExpr f)
  | _, .slice a lo len => .slice lo (2 ^ len) (d.elabExpr a)
  | _, .zext a w' => .zext (2 ^ w') (d.elabExpr a)
  | _, .sext (w := sw) a w' =>
      .sext (2 ^ (sw - 1)) (2 ^ w') (2 ^ w' - 2 ^ sw) (d.elabExpr a)

/-- Elaborate an action. -/
def Design.elabAct (d : Design) : Act → FAct
  | .skip => .skip
  | .seq a b => .seq (d.elabAct a) (d.elabAct b)
  | .ite c t e => .ite (d.elabExpr c) (d.elabAct t) (d.elabAct e)
  | .write _ r v => match d.regIdx r with
      | some i => .write i (d.elabExpr v)
      | none => .skip
  | .writeSlice totalWidth r lo fieldWidth _ v => match d.regIdx r with
      | some i => .writeSlice i totalWidth lo fieldWidth (d.elabExpr v)
      | none => .skip
  | .memWrite _ _ m _ addr data =>
      match d.memIdx m with
      | some k => .memWrite (d.memBase k) (d.elabExpr addr) (d.elabExpr data)
      | none => .skip

/-- Elaborate a whole design.  Do this once; then cycle for free. -/
def Design.elaborate (d : Design) : FastDesign where
  acts := (d.rules.map (fun r => d.elabAct r.body)).toArray
  slots := d.inputs.map (fun i => ((d.regIdx i.name).getD 0, i.name, i.width))
  nregs := d.regList.length
  memTotal := d.memTotal
  names := d.regList.toArray

/-! ## State conversion -/

/-- The flat memory cells of `σ`, memory by memory. -/
def Design.memCells (d : Design) (σ : St) : List Nat :=
  d.mems.flatMap
    (fun md => (List.range (2 ^ md.addrWidth)).map
      (fun a => (σ.mems md.name a md.dataWidth).toNat))

/-- Flatten a semantic state.  Defined *pointwise from* `σ`, so the
agreement invariant holds by construction. -/
def Design.ofSt (d : Design) (σ : St) : FastSt where
  regs := (d.regList.map (fun e => (σ.regs e.1 e.2).toNat)).toArray
  mems := (d.memCells σ).toArray

/-- The fast reset state. -/
def Design.fastReset (d : Design) : FastSt := d.ofSt d.reset

/-- Read a declared register/input coordinate back out of a flat state. -/
def FastDesign.peek (fd : FastDesign) (fs : FastSt) (n : String) : Option Nat :=
  match fd.names.findIdx? (fun e => e.1 == n) with
  | some i => some (fs.regs.getD i 0)
  | none => none

/-- Read a memory cell back out of a flat state. -/
def Design.peekMemCell (d : Design) (fs : FastSt) (n : String) (a : Nat) :
    Option Nat :=
  match d.memIdx n with
  | some k => some (fs.mems.getD (d.memBase k + a) 0)
  | none => none

/-- Inflate a flat state back into a `St`.  Junk coordinates (undeclared
names, off widths) read as zero; see the module docstring — this is a
convenience readback, not the object the correctness theorem is about. -/
def Design.toSt (d : Design) (fs : FastSt) : St where
  regs := fun n w =>
    match d.regIdx n with
    | some i => if (d.regEntry i).2 = w then BitVec.ofNat w (fs.regs.getD i 0) else 0#w
    | none => 0#w
  mems := fun n a w =>
    match d.memIdx n with
    | some k =>
        match d.mems[k]? with
        | some md =>
            if md.dataWidth = w ∧ a < 2 ^ md.addrWidth then
              BitVec.ofNat w (fs.mems.getD (d.memBase k + a) 0)
            else 0#w
        | none => 0#w
    | none => 0#w

/-! ## Open designs (D15) -/

/-- Drive the input coordinates from a valuation, by index. -/
def fastSetInputs (fd : FastDesign) (ι : InEnv) (fs : FastSt) : FastSt :=
  { fs with
    regs := fd.slots.foldl
      (fun r s => r.setIfInBounds s.1 ((ι s.2.1 s.2.2).toNat)) fs.regs }

/-- One cycle of an elaborated open design. -/
def fastCycleOpen (fd : FastDesign) (ι : InEnv) (fs : FastSt) : FastSt :=
  fastCycle fd (fastSetInputs fd ι fs)

/-- Run under an input trace. -/
def fastRunOpen (fd : FastDesign) (ιs : Nat → InEnv) : Nat → FastSt → FastSt
  | 0, fs => fs
  | n + 1, fs => fastRunOpen fd (fun k => ιs (k + 1)) n (fastCycleOpen fd (ιs 0) fs)

/-! ## The decidable side condition -/

/-- Duplicate-free check as a `Bool` (no kernel `decide` on 500-element
lists). -/
def nodupB : List String → Bool
  | [] => true
  | a :: t => !t.contains a && nodupB t

/-- Does register/input name `n` resolve to a declared coordinate of width
`w`? -/
def Design.regOkB (d : Design) (n : String) (w : Nat) : Bool :=
  match d.regIdx n with
  | some i => i < d.regList.length && (d.regEntry i).1 == n && (d.regEntry i).2 == w
  | none => false

/-- Does memory name `m` resolve, with data width `dw` and an address
expression of width `aw` no wider than the declared address width? -/
def Design.memOkB (d : Design) (m : String) (aw dw : Nat) : Bool :=
  match d.memIdx m with
  | some k =>
      match d.mems[k]? with
      | some md => md.name == m && md.dataWidth == dw && aw ≤ md.addrWidth
      | none => false
  | none => false

def Design.exprWFB (d : Design) : {w : Nat} → Expr w → Bool
  | _, .lit _ => true
  | w, .reg _ n => d.regOkB n w
  | dw, .memRead _ m (aw := aw) addr => d.memOkB m aw dw && d.exprWFB addr
  | _, .and a b => d.exprWFB a && d.exprWFB b
  | _, .or a b => d.exprWFB a && d.exprWFB b
  | _, .xor a b => d.exprWFB a && d.exprWFB b
  | _, .not a => d.exprWFB a
  | _, .add a b => d.exprWFB a && d.exprWFB b
  | _, .sub a b => d.exprWFB a && d.exprWFB b
  | _, .mul a b => d.exprWFB a && d.exprWFB b
  | _, .udiv a b => d.exprWFB a && d.exprWFB b
  | _, .urem a b => d.exprWFB a && d.exprWFB b
  | _, .shl a b => d.exprWFB a && d.exprWFB b
  | _, .shr a b => d.exprWFB a && d.exprWFB b
  | _, .eq a b => d.exprWFB a && d.exprWFB b
  | _, .ult a b => d.exprWFB a && d.exprWFB b
  | _, .slt a b => d.exprWFB a && d.exprWFB b
  | _, .mux c t f => d.exprWFB c && d.exprWFB t && d.exprWFB f
  | _, .slice a _ _ => d.exprWFB a
  | _, .zext a _ => d.exprWFB a
  | _, .sext a _ => d.exprWFB a

def Design.actWFB (d : Design) : Act → Bool
  | .skip => true
  | .seq a b => d.actWFB a && d.actWFB b
  | .ite c t e => d.exprWFB c && d.actWFB t && d.actWFB e
  | .write w r v => d.regOkB r w && d.exprWFB v
  | .writeSlice totalWidth r _ _ _ v =>
      d.regOkB r totalWidth && d.exprWFB v
  | .memWrite aw dw m _ addr data =>
      d.memOkB m aw dw && d.exprWFB addr && d.exprWFB data

/-- The FastEval side condition: names distinct, every read/write resolved
at the right width, every memory access within the declared address width.
Linear in the design; no `decide` in the kernel. -/
def Design.fastWFB (d : Design) : Bool :=
  nodupB (d.regList.map (·.1)) &&
  nodupB (d.mems.map (·.name)) &&
  d.rules.all (fun r => d.actWFB r.body) &&
  d.inputs.all (fun i => d.regOkB i.name i.width)


/-! ## Proof: array / list / arithmetic helpers -/

namespace FastEval

theorem getD_setIfInBounds_self {a : Array Nat} {i x : Nat} (h : i < a.size) :
    (a.setIfInBounds i x).getD i 0 = x := by
  simp [h]

theorem getD_setIfInBounds_ne {a : Array Nat} {i j x : Nat} (h : i ≠ j) :
    (a.setIfInBounds i x).getD j 0 = a.getD j 0 := by
  simp [Array.getD_getElem?, h]

theorem nodupB_sound : ∀ {l : List String}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | _ :: t, h => by
      simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
      refine List.nodup_cons.2 ⟨?_, nodupB_sound h.2⟩
      simpa using h.1

/-- Segments of the flat memory array are disjoint and ordered. -/
theorem memBaseOf_step (l : List MemDecl) : ∀ (k k' : Nat) (hk : k < l.length),
    k < k' → memBaseOf l k + 2 ^ (l[k]'hk).addrWidth ≤ memBaseOf l k' := by
  induction l with
  | nil => intro k k' hk _; simp at hk
  | cons m t ih =>
    intro k k' hk hlt
    match k, k' with
    | _, 0 => omega
    | 0, k'+1 => simp [memBaseOf]
    | k+1, k'+1 =>
      have h2 : k < t.length := by simp at hk; omega
      have := ih k k' h2 (by omega)
      simp only [memBaseOf, List.getElem_cons_succ]
      omega

theorem memBaseOf_lt_total (l : List MemDecl) (k : Nat) (hk : k < l.length) :
    memBaseOf l k + 2 ^ (l[k]'hk).addrWidth ≤ memBaseOf l l.length :=
  memBaseOf_step l k l.length hk hk

/-- Two distinct flat memory coordinates are distinct array indices. -/
theorem memBase_inj (l : List MemDecl) {k k' a a' : Nat}
    (hk : k < l.length) (hk' : k' < l.length)
    (ha : a < 2 ^ (l[k]'hk).addrWidth) (ha' : a' < 2 ^ (l[k']'hk').addrWidth)
    (hne : ¬ (k = k' ∧ a = a')) :
    memBaseOf l k + a ≠ memBaseOf l k' + a' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · have := memBaseOf_step l k k' hk h; omega
  · subst h
    have hne' : a ≠ a' := fun hh => hne ⟨rfl, hh⟩
    omega
  · have := memBaseOf_step l k' k hk' h; omega

/-! ### The flat memory image -/

/-- `memCells`-shaped list, generic in the cell function. -/
def cellsOf (f : MemDecl → Nat → Nat) (l : List MemDecl) : List Nat :=
  l.flatMap (fun md => (List.range (2 ^ md.addrWidth)).map (f md))

theorem cellsOf_length (f : MemDecl → Nat → Nat) :
    ∀ l : List MemDecl, (cellsOf f l).length = memBaseOf l l.length := by
  intro l
  induction l with
  | nil => simp [cellsOf, memBaseOf]
  | cons m t ih => simp [cellsOf, memBaseOf] at *; omega

theorem cellsOf_getD (f : MemDecl → Nat → Nat) :
    ∀ (l : List MemDecl) (k : Nat) (md : MemDecl), l[k]? = some md →
      ∀ a, a < 2 ^ md.addrWidth →
        (cellsOf f l).getD (memBaseOf l k + a) 0 = f md a := by
  intro l
  induction l with
  | nil => intro k md h; simp at h
  | cons m t ih =>
    intro k md hmd a ha
    match k with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hmd
      subst hmd
      have hlen : ((List.range (2 ^ m.addrWidth)).map (f m)).length
          = 2 ^ m.addrWidth := by simp
      simp only [cellsOf, List.flatMap_cons, memBaseOf, Nat.zero_add,
        List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
      simp [ha]
    | k+1 =>
      simp only [List.getElem?_cons_succ] at hmd
      have hlen : ((List.range (2 ^ m.addrWidth)).map (f m)).length
          = 2 ^ m.addrWidth := by simp
      have hih := ih k md hmd a ha
      simp only [cellsOf, List.flatMap_cons, memBaseOf,
        List.getD_eq_getElem?_getD] at hih ⊢
      rw [List.getElem?_append_right (by omega), hlen,
        show 2 ^ m.addrWidth + memBaseOf t k + a - 2 ^ m.addrWidth
          = memBaseOf t k + a from by omega]
      exact hih

theorem regEntry_eq (d : Design) {i : Nat} (hi : i < d.regList.length) :
    d.regEntry i = d.regList[i] := by
  simp [Design.regEntry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-! ## The agreement invariant -/

end FastEval

/-- The flat state `fs` represents the semantic state `σ` on every declared
coordinate of `d`. -/
structure Agree (d : Design) (fs : FastSt) (σ : St) : Prop where
  regsSize : fs.regs.size = d.regList.length
  memsSize : fs.mems.size = d.memTotal
  regs : ∀ i, i < d.regList.length →
    fs.regs.getD i 0 = (σ.regs (d.regEntry i).1 (d.regEntry i).2).toNat
  mems : ∀ k md, d.mems[k]? = some md → ∀ a, a < 2 ^ md.addrWidth →
    fs.mems.getD (d.memBase k + a) 0 = (σ.mems md.name a md.dataWidth).toNat

theorem agree_ofSt (d : Design) (σ : St) : Agree d (d.ofSt σ) σ where
  regsSize := by simp [Design.ofSt]
  memsSize := by
    simp only [Design.ofSt, List.size_toArray, Design.memTotal, Design.memCells]
    exact FastEval.cellsOf_length _ d.mems
  regs := by
    intro i hi
    rw [FastEval.regEntry_eq d hi]
    simp [Design.ofSt, List.getElem?_map, List.getElem?_eq_getElem hi]
  mems := by
    intro k md hmd a ha
    simp only [Design.ofSt, Design.memCells, Design.memBase]
    have := FastEval.cellsOf_getD
      (fun md a => (σ.mems md.name a md.dataWidth).toNat) d.mems k md hmd a ha
    simpa [FastEval.cellsOf, List.getD_eq_getElem?_getD] using this


namespace FastEval

/-! ## Proof: the side condition gives back what the induction needs -/

theorem regOkB_sound {d : Design} {n : String} {w : Nat} (h : d.regOkB n w = true) :
    ∃ i, d.regIdx n = some i ∧ i < d.regList.length ∧
      (d.regEntry i).1 = n ∧ (d.regEntry i).2 = w := by
  unfold Design.regOkB at h
  cases hidx : d.regIdx n with
  | none => simp [hidx] at h
  | some i =>
    simp only [hidx, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨i, rfl, h.1.1, h.1.2, h.2⟩

theorem memOkB_sound {d : Design} {m : String} {aw dw : Nat}
    (h : d.memOkB m aw dw = true) :
    ∃ k md, d.memIdx m = some k ∧ d.mems[k]? = some md ∧
      md.name = m ∧ md.dataWidth = dw ∧ aw ≤ md.addrWidth := by
  unfold Design.memOkB at h
  cases hidx : d.memIdx m with
  | none => simp [hidx] at h
  | some k =>
    simp only [hidx] at h
    cases hmd : d.mems[k]? with
    | none => simp [hmd] at h
    | some md =>
      simp only [hmd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact ⟨k, md, rfl, hmd, h.1.1, h.1.2, h.2⟩

/-! ## Typed, declaration-resolved state views

Machine environments should not recover generated state through another table
of string names and widths.  The typed handles already carry that information.
The slots below resolve a handle once, retain the facts established by the
design's declarations, and reduce every subsequent read to an array access.

The proof fields are erased from executable code.  A missing handle or width
mismatch therefore fails during preparation; it cannot silently read slot zero
or manufacture a zero value in the simulation loop. -/

/-- A typed register handle resolved into the flat generated-state layout. -/
structure RegSlot (d : Design) {w : Nat} (r : Reg w) where
  idx : Nat
  index_eq : d.regIdx r.name = some idx
  index_lt : idx < d.regList.length
  name_eq : (d.regEntry idx).1 = r.name
  width_eq : (d.regEntry idx).2 = w

/-- Resolve a typed register handle against a design, failing on absence or a
width disagreement. -/
def regSlot? (d : Design) {w : Nat} (r : Reg w) : Option (RegSlot d r) :=
  match hi : d.regIdx r.name with
  | none => none
  | some i =>
      if hlt : i < d.regList.length then
        if hn : (d.regEntry i).1 = r.name then
          if hw : (d.regEntry i).2 = w then
            some ⟨i, hi, hlt, hn, hw⟩
          else none
        else none
      else none

/-- IO preparation adapter with a specific declaration error. -/
def prepareRegSlot (d : Design) {w : Nat} (r : Reg w) :
    IO (RegSlot d r) :=
  match regSlot? d r with
  | some slot => pure slot
  | none => throw <| IO.userError
      s!"{d.name}: register view does not resolve: {r.name} : {w}"

/-- Read a resolved register as a natural number. -/
@[inline] def RegSlot.readNat {d : Design} {w : Nat} {r : Reg w}
    (slot : RegSlot d r) (fs : FastSt) : Nat :=
  fs.regs.getD slot.idx 0

/-- Read a resolved register at the width carried by its typed handle. -/
@[inline] def RegSlot.read {d : Design} {w : Nat} {r : Reg w}
    (slot : RegSlot d r) (fs : FastSt) : BitVec w :=
  BitVec.ofNat w (slot.readNat fs)

/-- Inflating a flat state reads a resolved typed register from exactly the
same array slot.  This supports compact System runners that delegate endpoint
planning to the public semantic wiring without copying memory arrays. -/
theorem RegSlot.read_toSt {d : Design} {w : Nat} {r : Reg w}
    (slot : RegSlot d r) (fs : FastSt) :
    slot.read fs = (d.toSt fs).regs r.name w := by
  simp [RegSlot.read, RegSlot.readNat, Design.toSt, slot.index_eq,
    slot.width_eq]

/-- A resolved typed-register read is the corresponding semantic coordinate
whenever the generated and reference states agree. -/
theorem RegSlot.readNat_eq {d : Design} {w : Nat} {r : Reg w}
    (slot : RegSlot d r) {fs : FastSt} {sigma : St} (ha : Agree d fs sigma) :
    slot.readNat fs = (sigma.regs r.name w).toNat := by
  rw [RegSlot.readNat, ha.regs slot.idx slot.index_lt, slot.name_eq,
    slot.width_eq]

/-- Bit-vector form of `readNat_eq`, retaining the register's static width. -/
theorem RegSlot.read_eq {d : Design} {w : Nat} {r : Reg w}
    (slot : RegSlot d r) {fs : FastSt} {sigma : St} (ha : Agree d fs sigma) :
    slot.read fs = sigma.regs r.name w := by
  apply BitVec.toNat_inj.mp
  simp only [RegSlot.read, BitVec.toNat_ofNat]
  rw [slot.readNat_eq ha, Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- A typed memory handle resolved into the flat generated-state layout. -/
structure MemSlot (d : Design) {aw dw : Nat} (m : Mem aw dw) where
  idx : Nat
  decl : MemDecl
  index_eq : d.memIdx m.name = some idx
  decl_eq : d.mems[idx]? = some decl
  name_eq : decl.name = m.name
  addr_width_eq : decl.addrWidth = aw
  data_width_eq : decl.dataWidth = dw

/-- Resolve a typed memory handle against a design.  Address and data widths
must both match exactly; unlike expression elaboration, a state view does not
permit a narrower address expression. -/
def memSlot? (d : Design) {aw dw : Nat} (m : Mem aw dw) :
    Option (MemSlot d m) :=
  match hi : d.memIdx m.name with
  | none => none
  | some i =>
      match hd : d.mems[i]? with
      | none => none
      | some md =>
          if hn : md.name = m.name then
            if ha : md.addrWidth = aw then
              if hw : md.dataWidth = dw then
                some ⟨i, md, hi, hd, hn, ha, hw⟩
              else none
            else none
          else none

/-- IO preparation adapter with a specific declaration error. -/
def prepareMemSlot (d : Design) {aw dw : Nat} (m : Mem aw dw) :
    IO (MemSlot d m) :=
  match memSlot? d m with
  | some slot => pure slot
  | none => throw <| IO.userError
      s!"{d.name}: memory view does not resolve: {m.name} : {aw} -> {dw}"

/-- Read a resolved memory cell as a natural number. -/
@[inline] def MemSlot.readNat {d : Design} {aw dw : Nat} {m : Mem aw dw}
    (slot : MemSlot d m) (fs : FastSt) (addr : BitVec aw) : Nat :=
  fs.mems.getD (d.memBase slot.idx + addr.toNat) 0

/-- Read a resolved memory cell at the data width carried by its handle. -/
@[inline] def MemSlot.read {d : Design} {aw dw : Nat} {m : Mem aw dw}
    (slot : MemSlot d m) (fs : FastSt) (addr : BitVec aw) : BitVec dw :=
  BitVec.ofNat dw (slot.readNat fs addr)

/-- A typed memory-slot read is the corresponding semantic coordinate whenever
the generated and reference states agree. -/
theorem MemSlot.readNat_eq {d : Design} {aw dw : Nat} {m : Mem aw dw}
    (slot : MemSlot d m) {fs : FastSt} {sigma : St} (ha : Agree d fs sigma)
    (addr : BitVec aw) :
    slot.readNat fs addr = (sigma.mems m.name addr.toNat dw).toNat := by
  rw [MemSlot.readNat,
    ha.mems slot.idx slot.decl slot.decl_eq addr.toNat]
  · rw [slot.name_eq, slot.data_width_eq]
  · rw [slot.addr_width_eq]
    exact addr.isLt

/-! ## Proof: shift guards -/

theorem shiftLeft_mod_eq_zero (x : Nat) {n w : Nat} (h : w ≤ n) :
    (x <<< n) % 2 ^ w = 0 := by
  rw [Nat.shiftLeft_eq]
  have hp : 2 ^ n = 2 ^ (n - w) * 2 ^ w := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hp, ← Nat.mul_assoc]
  exact Nat.mul_mod_left _ _

theorem shiftRight_eq_zero {x w n : Nat} (hx : x < 2 ^ w) (h : w ≤ n) :
    x >>> n = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h))

/-! ## Proof: expressions -/

theorem elabExpr_eval {d : Design} {fs : FastSt} {σ : St} (ha : Agree d fs σ) :
    ∀ (w : Nat) (e : Expr w), d.exprWFB e = true →
      (d.elabExpr e).eval fs.regs fs.mems = (e.eval σ).toNat := by
  intro w e
  induction e with
  | lit v => intro _; rfl
  | reg w n =>
    intro hwf
    simp only [Design.exprWFB] at hwf
    obtain ⟨i, hidx, hlt, hn, hw⟩ := regOkB_sound hwf
    simp only [Design.elabExpr, hidx, FExpr.eval]
    rw [ha.regs i hlt, hn, hw]
    rfl
  | memRead dw m addr ih =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    obtain ⟨k, md, hk, hmd, hname, hdw, haw⟩ := memOkB_sound hwf.1
    have hlt : ((addr.eval σ).toNat) < 2 ^ md.addrWidth :=
      Nat.lt_of_lt_of_le (addr.eval σ).isLt (Nat.pow_le_pow_right (by omega) haw)
    simp only [Design.elabExpr, hk, FExpr.eval]
    rw [ih hwf.2, ha.mems k md hmd _ hlt, hname, hdw]
    rfl
  | and a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_and]
  | or a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_or]
  | xor a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_xor]
  | not a ih =>
    intro hwf
    simp only [Design.exprWFB] at hwf
    simp only [Design.elabExpr, FExpr.eval, ih hwf, Expr.eval, BitVec.toNat_not]
  | add a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_add]
  | sub a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_sub]
  | mul a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_mul]
  | udiv a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_udiv]
  | urem a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_umod]
  | shl a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_shiftLeft]
    split
    · rfl
    · exact (shiftLeft_mod_eq_zero _ (by omega)).symm
  | shr a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.toNat_ushiftRight]
    split
    · rfl
    · exact (shiftRight_eq_zero (a.eval σ).isLt (by omega)).symm
  | eq a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval]
    by_cases h : a.eval σ = b.eval σ
    · simp [h]
    · have hne : (a.eval σ).toNat ≠ (b.eval σ).toNat :=
        fun hh => h (BitVec.toNat_inj.mp hh)
      simp [h, hne]
  | ult a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.ult_eq_decide]
    by_cases hlt : (a.eval σ).toNat < (b.eval σ).toNat <;> simp [hlt]
  | slt a b iha ihb =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, iha hwf.1, ihb hwf.2, Expr.eval,
      BitVec.slt_eq_ult, BitVec.ult_eq_decide, BitVec.msb_eq_decide]
    split <;> simp_all
  | mux c t f ihc iht ihf =>
    intro hwf
    simp only [Design.exprWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabExpr, FExpr.eval, ihc hwf.1.1, iht hwf.1.2, ihf hwf.2,
      Expr.eval]
    by_cases h : c.eval σ = 1#1
    · simp [h]
    · have : (c.eval σ).toNat ≠ 1 := fun hh => h (BitVec.toNat_inj.mp hh)
      simp [h, this]
  | slice a lo len ih =>
    intro hwf
    simp only [Design.exprWFB] at hwf
    simp only [Design.elabExpr, FExpr.eval, ih hwf, Expr.eval,
      BitVec.extractLsb', BitVec.toNat_ofNat]
  | zext a w' ih =>
    intro hwf
    simp only [Design.exprWFB] at hwf
    simp only [Design.elabExpr, FExpr.eval, ih hwf, Expr.eval,
      BitVec.toNat_setWidth]
  | sext a w' ih =>
    intro hwf
    simp only [Design.exprWFB] at hwf
    simp only [Design.elabExpr, FExpr.eval, ih hwf, Expr.eval,
      BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
    split <;> simp_all <;> (intro _; omega)


/-! ## Proof: actions -/

theorem nodup_getElem_ne {α β : Type} [DecidableEq β] {l : List α} {f : α → β}
    (h : (l.map f).Nodup) {p q : Nat} (hp : p < l.length) (hq : q < l.length)
    (hne : p ≠ q) : f (l[p]'hp) ≠ f (l[q]'hq) := by
  intro heq
  refine hne ?_
  have hp' : p < (l.map f).length := by simpa using hp
  have hq' : q < (l.map f).length := by simpa using hq
  have hgg : (l.map f)[p]'hp' = (l.map f)[q]'hq' := by simpa using heq
  rcases Nat.lt_trichotomy p q with hlt | he | hlt
  · exact absurd hgg (List.pairwise_iff_getElem.mp h p q hp' hq' hlt)
  · exact he
  · exact absurd hgg.symm (List.pairwise_iff_getElem.mp h q p hq' hp' hlt)

theorem mems_idx {d : Design} {k : Nat} {md : MemDecl} (h : d.mems[k]? = some md) :
    ∃ hk : k < d.mems.length, d.mems[k] = md := List.getElem?_eq_some_iff.mp h

theorem elabAct_run {d : Design} (hnd : (d.regList.map (·.1)).Nodup)
    (hmnd : (d.mems.map (·.name)).Nodup)
    {fs : FastSt} {σ : St} (ha : Agree d fs σ) :
    ∀ (a : Act) (facc : FastSt) (τ : St), d.actWFB a = true → Agree d facc τ →
      Agree d ((d.elabAct a).run fs.regs fs.mems facc) (a.run σ τ) := by
  intro a
  induction a with
  | skip => intro facc τ _ hacc; exact hacc
  | seq x y ihx ihy =>
    intro facc τ hwf hacc
    simp only [Design.actWFB, Bool.and_eq_true] at hwf
    exact ihy _ _ hwf.2 (ihx _ _ hwf.1 hacc)
  | ite c t e iht ihe =>
    intro facc τ hwf hacc
    simp only [Design.actWFB, Bool.and_eq_true] at hwf
    simp only [Design.elabAct, FAct.run, Act.run, elabExpr_eval ha _ c hwf.1.1]
    by_cases hc : c.eval σ = 1#1
    · simp only [hc, BitVec.toNat_ofNat]
      exact iht _ _ hwf.1.2 hacc
    · have hne1 : (c.eval σ).toNat ≠ 1 := fun hh => hc (BitVec.toNat_inj.mp hh)
      simp only [hc, hne1, if_false]
      exact ihe _ _ hwf.2 hacc
  | write w r v =>
    intro facc τ hwf hacc
    simp only [Design.actWFB, Bool.and_eq_true] at hwf
    obtain ⟨i, hidx, hlt, hn, hw⟩ := regOkB_sound hwf.1
    have hev := elabExpr_eval ha _ v hwf.2
    simp only [Design.elabAct, hidx, FAct.run, Act.run, hev]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hacc.regsSize
    · simpa using hacc.memsSize
    · intro j hj
      by_cases hij : i = j
      · subst hij
        rw [getD_setIfInBounds_self (by rw [hacc.regsSize]; exact hlt), hn, hw]
        simp [RegEnv.set]
      · rw [getD_setIfInBounds_ne hij, hacc.regs j hj]
        have hrne : (d.regEntry j).1 ≠ r := by
          rw [regEntry_eq d hj]
          have : (d.regEntry i).1 = (d.regList[i]'hlt).1 := by rw [regEntry_eq d hlt]
          rw [← hn, this]
          exact nodup_getElem_ne (f := fun e => e.1) hnd hj hlt (fun hh => hij hh.symm)
        simp [RegEnv.set, hrne]
    · intro k md hmd a2 ha2
      simpa using hacc.mems k md hmd a2 ha2
  | writeSlice totalWidth r lo fieldWidth inBounds v =>
    intro facc τ hwf hacc
    simp only [Design.actWFB, Bool.and_eq_true] at hwf
    obtain ⟨i, hidx, hlt, hn, hw⟩ := regOkB_sound hwf.1
    have hev := elabExpr_eval ha _ v hwf.2
    simp only [Design.elabAct, hidx, FAct.run, Act.run, hev]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hacc.regsSize
    · simpa using hacc.memsSize
    · intro j hj
      by_cases hij : i = j
      · subst hij
        rw [getD_setIfInBounds_self (by rw [hacc.regsSize]; exact hlt), hn, hw,
          hacc.regs i hlt, hn, hw]
        simp [RegEnv.set]
      · rw [getD_setIfInBounds_ne hij, hacc.regs j hj]
        have hrne : (d.regEntry j).1 ≠ r := by
          rw [regEntry_eq d hj]
          have : (d.regEntry i).1 = (d.regList[i]'hlt).1 := by
            rw [regEntry_eq d hlt]
          rw [← hn, this]
          exact nodup_getElem_ne (f := fun e => e.1) hnd hj hlt
            (fun hh => hij hh.symm)
        simp [RegEnv.set, hrne]
    · intro k md hmd a2 ha2
      simpa using hacc.mems k md hmd a2 ha2
  | memWrite aw dw m port addr data =>
    intro facc τ hwf hacc
    simp only [Design.actWFB, Bool.and_eq_true] at hwf
    obtain ⟨k, md, hk, hmd, hname, hdw, haw⟩ := memOkB_sound hwf.1.1
    obtain ⟨hklen, hkget⟩ := mems_idx hmd
    have hea := elabExpr_eval ha _ addr hwf.1.2
    have hed := elabExpr_eval ha _ data hwf.2
    have hlt : ((addr.eval σ).toNat) < 2 ^ md.addrWidth :=
      Nat.lt_of_lt_of_le (addr.eval σ).isLt (Nat.pow_le_pow_right (by omega) haw)
    have hbound : d.memBase k + (addr.eval σ).toNat < facc.mems.size := by
      rw [hacc.memsSize]
      have := memBaseOf_lt_total d.mems k hklen
      rw [hkget] at this
      simpa [Design.memBase, Design.memTotal] using Nat.lt_of_lt_of_le
        (by omega : memBaseOf d.mems k + (addr.eval σ).toNat
              < memBaseOf d.mems k + 2 ^ md.addrWidth) this
    simp only [Design.elabAct, hk, FAct.run, Act.run, hea, hed]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hacc.regsSize
    · simpa using hacc.memsSize
    · intro j hj; simpa using hacc.regs j hj
    · intro k' md' hmd' a2 ha2
      obtain ⟨hklen', hkget'⟩ := mems_idx hmd'
      by_cases hkk : k' = k
      · subst hkk
        have hmm : md' = md := by
          rw [hmd'] at hmd; exact Option.some.inj hmd
        subst hmm
        by_cases haa : a2 = (addr.eval σ).toNat
        · subst haa
          rw [getD_setIfInBounds_self hbound, hname, hdw]
          simp [MemEnv.set]
        · rw [getD_setIfInBounds_ne (by omega), hacc.mems k' md' hmd' a2 ha2]
          simp [MemEnv.set, haa]
      · have hnn : md'.name ≠ md.name := by
          rw [← hkget, ← hkget']
          exact nodup_getElem_ne (f := fun x => x.name) hmnd hklen' hklen hkk
        have hidxne : d.memBase k' + a2 ≠ d.memBase k + (addr.eval σ).toNat := by
          simp only [Design.memBase]
          refine memBase_inj d.mems hklen' hklen ?_ ?_ (fun hh => hkk hh.1)
          · rw [hkget']; exact ha2
          · rw [hkget]; exact hlt
        rw [getD_setIfInBounds_ne (Ne.symm hidxne), hacc.mems k' md' hmd' a2 ha2]
        have : md'.name ≠ m := by rw [← hname]; exact hnn
        simp [MemEnv.set, this]


/-! ## Proof: the cycle -/

theorem fastWFB_parts {d : Design} (h : d.fastWFB = true) :
    (d.regList.map (·.1)).Nodup ∧ (d.mems.map (·.name)).Nodup ∧
    (∀ r ∈ d.rules, d.actWFB r.body = true) ∧
    (∀ i ∈ d.inputs, d.regOkB i.name i.width = true) := by
  simp only [Design.fastWFB, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨nodupB_sound h.1.1.1, nodupB_sound h.1.1.2,
         fun r hr => h.1.2 r hr, fun i hi => h.2 i hi⟩

theorem fold_agree {d : Design} (hnd : (d.regList.map (·.1)).Nodup)
    (hmnd : (d.mems.map (·.name)).Nodup) {fs : FastSt} {σ : St}
    (ha : Agree d fs σ) :
    ∀ (rs : List Rule), (∀ r ∈ rs, d.actWFB r.body = true) →
      ∀ (facc : FastSt) (τ : St), Agree d facc τ →
        Agree d ((rs.map (fun r => d.elabAct r.body)).foldl
                  (fun acc a => FAct.run fs.regs fs.mems a acc) facc)
                (rs.foldl (fun acc r => r.body.run σ acc) τ) := by
  intro rs
  induction rs with
  | nil => intro _ facc τ hacc; exact hacc
  | cons r t ih =>
    intro hok facc τ hacc
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun x hx => hok x (List.mem_cons_of_mem _ hx)) _ _
      (elabAct_run hnd hmnd ha r.body facc τ (hok r (List.mem_cons_self ..)) hacc)

/-- **The correctness theorem.**  One `fastCycle` of the elaborated design
reproduces one `Design.cycle` on every declared coordinate. -/
theorem fastCycle_eq (d : Design) (hwf : d.fastWFB = true) (fs : FastSt) (σ : St)
    (ha : Agree d fs σ) : Agree d (fastCycle d.elaborate fs) (d.cycle σ) := by
  obtain ⟨hnd, hmnd, hrules, _⟩ := fastWFB_parts hwf
  have := fold_agree hnd hmnd ha d.rules hrules fs σ ha
  simpa [fastCycle, Design.elaborate, Design.cycle, List.foldl_toArray] using this

/-- `fastRun` reproduces `Design.run`. -/
theorem fastRun_eq (d : Design) (hwf : d.fastWFB = true) :
    ∀ (n : Nat) (fs : FastSt) (σ : St), Agree d fs σ →
      Agree d (fastRun d.elaborate n fs) (d.run n σ) := by
  intro n
  induction n with
  | zero => intro fs σ ha; exact ha
  | succ n ih =>
    intro fs σ ha
    exact ih _ _ (fastCycle_eq d hwf fs σ ha)

/-! ## Proof: inputs (D15) -/

/-- The register half of `Agree`. -/
def RegAgree (d : Design) (ra : Array Nat) (ρ : RegEnv) : Prop :=
  ra.size = d.regList.length ∧
  ∀ j, j < d.regList.length → ra.getD j 0 = (ρ (d.regEntry j).1 (d.regEntry j).2).toNat

theorem regAgree_set {d : Design} (hnd : (d.regList.map (·.1)).Nodup)
    {ra : Array Nat} {ρ : RegEnv} (h : RegAgree d ra ρ) {n : String} {w : Nat}
    (hok : d.regOkB n w = true) (v : BitVec w) :
    RegAgree d (ra.setIfInBounds ((d.regIdx n).getD 0) v.toNat) (ρ.set n v) := by
  obtain ⟨i, hidx, hlt, hnm, hw⟩ := regOkB_sound hok
  simp only [hidx, Option.getD_some]
  refine ⟨by simpa using h.1, ?_⟩
  intro j hj
  by_cases hij : i = j
  · subst hij
    rw [getD_setIfInBounds_self (by rw [h.1]; exact hlt), hnm, hw]
    simp [RegEnv.set]
  · rw [getD_setIfInBounds_ne hij, h.2 j hj]
    have hrne : (d.regEntry j).1 ≠ n := by
      rw [regEntry_eq d hj]
      have hh : (d.regEntry i).1 = (d.regList[i]'hlt).1 := by rw [regEntry_eq d hlt]
      rw [← hnm, hh]
      exact nodup_getElem_ne (f := fun e => e.1) hnd hj hlt (fun x => hij x.symm)
    simp [RegEnv.set, hrne]

theorem setInputs_agree {d : Design} (hnd : (d.regList.map (·.1)).Nodup)
    (ι : InEnv) :
    ∀ (ins : List InputDecl), (∀ i ∈ ins, d.regOkB i.name i.width = true) →
    ∀ (ra : Array Nat) (ρ : RegEnv), RegAgree d ra ρ →
      RegAgree d
        ((ins.map (fun i => ((d.regIdx i.name).getD 0, i.name, i.width))).foldl
          (fun r s => r.setIfInBounds s.1 ((ι s.2.1 s.2.2).toNat)) ra)
        (ins.foldl (fun ρ i => ρ.set i.name (ι i.name i.width)) ρ) := by
  intro ins
  induction ins with
  | nil => intro _ ra ρ h; exact h
  | cons x t ih =>
    intro hok ra ρ h
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun i hi => hok i (List.mem_cons_of_mem _ hi)) _ _
      (regAgree_set hnd h (hok x (List.mem_cons_self ..)) (ι x.name x.width))

theorem fastSetInputs_eq (d : Design) (hwf : d.fastWFB = true) (ι : InEnv)
    (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (fastSetInputs d.elaborate ι fs) (σ.setInputs d.inputs ι) := by
  obtain ⟨hnd, _, _, hins⟩ := fastWFB_parts hwf
  have hr := setInputs_agree hnd ι d.inputs hins fs.regs σ.regs ⟨ha.regsSize, ha.regs⟩
  exact { regsSize := hr.1
          memsSize := ha.memsSize
          regs := hr.2
          mems := ha.mems }

/-- The open-design correctness theorem (D15). -/
theorem fastCycleOpen_eq (d : Design) (hwf : d.fastWFB = true) (ι : InEnv)
    (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (fastCycleOpen d.elaborate ι fs) (d.cycleOpen ι σ) :=
  fastCycle_eq d hwf _ _ (fastSetInputs_eq d hwf ι fs σ ha)

theorem fastRunOpen_eq (d : Design) (hwf : d.fastWFB = true) :
    ∀ (n : Nat) (ιs : Nat → InEnv) (fs : FastSt) (σ : St), Agree d fs σ →
      Agree d (fastRunOpen d.elaborate ιs n fs) (d.runOpen ιs n σ) := by
  intro n
  induction n with
  | zero => intro _ fs σ ha; exact ha
  | succ n ih =>
    intro ιs fs σ ha
    exact ih _ _ _ (fastCycleOpen_eq d hwf (ιs 0) fs σ ha)

/-! ## Readback -/

theorem agree_fastReset (d : Design) : Agree d d.fastReset d.reset :=
  agree_ofSt d d.reset

/-! ## The public verified-simulator object

`FastDesign` is deliberately just executable data.  `VerifiedSimulator`
packages the one design-specific proof needed to connect that data back to
the reference semantics.  A machine can therefore publish one object rather
than repeat applications of the generic correctness theorems at every call
site.

The theorem names use `_eq`, but their conclusion is `Agree`: this is the
extensional equality available between the flat state and `St`, whose
closure-based environments may also contain undeclared, unobservable
coordinates. -/

/-- A simulator derived from `d`, together with the checked condition that
makes its evaluator a proved view of `Design.cycle` / `Design.cycleOpen`. -/
structure VerifiedSimulator (d : Design) where
  wf : d.fastWFB = true

namespace VerifiedSimulator

/-- The generated, index-resolved evaluator for this simulator. -/
def fast {d : Design} (_ : VerifiedSimulator d) : FastDesign := d.elaborate

/-- The generated flat reset state. -/
def reset {d : Design} (_ : VerifiedSimulator d) : FastSt := d.fastReset

/-- Execute one closed-design cycle. -/
def cycle {d : Design} (sim : VerifiedSimulator d) (fs : FastSt) : FastSt :=
  fastCycle sim.fast fs

/-- Execute one open-design cycle. -/
def cycleOpen {d : Design} (sim : VerifiedSimulator d) (ι : InEnv)
    (fs : FastSt) : FastSt :=
  fastCycleOpen sim.fast ι fs

/-- Execute `n` closed-design cycles. -/
def run {d : Design} (sim : VerifiedSimulator d) (n : Nat) (fs : FastSt) : FastSt :=
  fastRun sim.fast n fs

/-- Execute `n` open-design cycles. -/
def runOpen {d : Design} (sim : VerifiedSimulator d) (ιs : Nat → InEnv)
    (n : Nat) (fs : FastSt) : FastSt :=
  fastRunOpen sim.fast ιs n fs

/-- The generated closed evaluator equals the reference cycle on every
declared coordinate. -/
theorem cycle_eq {d : Design} (sim : VerifiedSimulator d) (fs : FastSt) (σ : St)
    (ha : Agree d fs σ) : Agree d (sim.cycle fs) (d.cycle σ) := by
  simpa [cycle, fast] using fastCycle_eq d sim.wf fs σ ha

/-- The generated open evaluator equals the reference open cycle on every
declared coordinate. -/
theorem cycleOpen_eq {d : Design} (sim : VerifiedSimulator d) (ι : InEnv)
    (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (sim.cycleOpen ι fs) (d.cycleOpen ι σ) := by
  simpa [cycleOpen, fast] using fastCycleOpen_eq d sim.wf ι fs σ ha

/-- The generated closed evaluator equals the reference run on every
declared coordinate. -/
theorem run_eq {d : Design} (sim : VerifiedSimulator d) (n : Nat)
    (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (sim.run n fs) (d.run n σ) := by
  simpa [run, fast] using fastRun_eq d sim.wf n fs σ ha

/-- The generated open evaluator equals the reference open run on every
declared coordinate. -/
theorem runOpen_eq {d : Design} (sim : VerifiedSimulator d) (n : Nat)
    (ιs : Nat → InEnv) (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (sim.runOpen ιs n fs) (d.runOpen ιs n σ) := by
  simpa [runOpen, fast] using fastRunOpen_eq d sim.wf n ιs fs σ ha

/-- Direct machine-facing equality from generated reset through a closed
run. -/
theorem runFromReset_eq {d : Design} (sim : VerifiedSimulator d) (n : Nat) :
    Agree d (sim.run n sim.reset) (d.run n d.reset) :=
  sim.run_eq n _ _ (agree_fastReset d)

/-- Direct machine-facing equality from generated reset through an open
run. -/
theorem runOpenFromReset_eq {d : Design} (sim : VerifiedSimulator d) (n : Nat)
    (ιs : Nat → InEnv) :
    Agree d (sim.runOpen ιs n sim.reset) (d.runOpen ιs n d.reset) :=
  sim.runOpen_eq n ιs _ _ (agree_fastReset d)

end VerifiedSimulator

/-- What an oracle consumes: the flat state reproduces every declared
register/input coordinate exactly. -/
theorem Agree.peekReg {d : Design} {fs : FastSt} {σ : St} (ha : Agree d fs σ)
    {n : String} {w : Nat} (hok : d.regOkB n w = true) :
    fs.regs.getD ((d.regIdx n).getD 0) 0 = (σ.regs n w).toNat := by
  obtain ⟨i, hidx, hlt, hnm, hw⟩ := regOkB_sound hok
  simp only [hidx, Option.getD_some]
  rw [ha.regs i hlt, hnm, hw]

/-- …and every declared memory cell. -/
theorem Agree.peekMem {d : Design} {fs : FastSt} {σ : St} (ha : Agree d fs σ)
    {k : Nat} {md : MemDecl} (hmd : d.mems[k]? = some md)
    {a : Nat} (haa : a < 2 ^ md.addrWidth) :
    fs.mems.getD (d.memBase k + a) 0 = (σ.mems md.name a md.dataWidth).toNat :=
  ha.mems k md hmd a haa

end FastEval

/-! ## Executable readback and the corroboration harness -/

/-- All declared register/input coordinates of a flat state, as
`name = value` pairs in declaration order. -/
def Design.fastRegs (d : Design) (fs : FastSt) : List (String × Nat) :=
  d.regList.zipIdx.map (fun (e, i) => (e.1, fs.regs.getD i 0))

/-- All declared memory cells of a flat state. -/
def Design.fastMem (d : Design) (fs : FastSt) (n : String) : List Nat :=
  match d.memIdx n with
  | some k =>
      match d.mems[k]? with
      | some md => (List.range (2 ^ md.addrWidth)).map
          (fun a => fs.mems.getD (d.memBase k + a) 0)
      | none => []
  | none => []

/-- Differential harness: run `fastCycle` and the reference `Design.cycle`
in lockstep for `depth` cycles under the input trace `ιs`, comparing every
declared register/input coordinate and every declared memory cell after
each cycle.  Independent of the proof — a `decide`-free corroboration that
the two evaluators agree on the designs we ship. -/
def Design.lockstep (d : Design) (depth : Nat)
    (ιs : Nat → InEnv := fun _ _ w => 0#w) : IO Bool := do
  let fd := d.elaborate
  let result ← Loom.Runner.run
    { label := s!"{d.name} FastEval/semantics", steps := depth }
    (d.fastReset, d.reset) fun c state => do
      let fs := fastCycleOpen fd (ιs c) state.1
      let σ := d.cycleOpen (ιs c) state.2
      let mut events : List Loom.Runner.Event := []
      for (e, i) in d.regList.zipIdx do
        let actual := fs.regs.getD i 0
        let expected := (σ.regs e.1 e.2).toNat
        if actual ≠ expected then
          let event : Loom.Runner.Event :=
            { subject := e.1
              actual := some (toString actual)
              expected := some (toString expected) }
          events := events ++ [event]
      for (md, k) in d.mems.zipIdx do
        for a in List.range (2 ^ md.addrWidth) do
          let actual := fs.mems.getD (d.memBase k + a) 0
          let expected := (σ.mems md.name a md.dataWidth).toNat
          if actual ≠ expected then
            let event : Loom.Runner.Event :=
              { subject := s!"{md.name}[{a}]"
                actual := some (toString actual)
                expected := some (toString expected) }
            events := events ++ [event]
      return ((fs, σ), { mismatches := events })
  return result.verdict == Loom.Runner.Verdict.pass

/-- A cheap deterministic pseudo-random input trace for the harness: an
xorshift-ish LFSR over the cycle index, sliced per input width. -/
def randomInEnv (seed : Nat) : Nat → InEnv := fun c n w =>
  let h := (seed + 1) * 2654435761 + (c + 1) * 40503 + n.length * 97 + n.foldl (fun a ch => a * 31 + ch.toNat) 7
  BitVec.ofNat w (h % 4294967296)

end Loom.Hw
