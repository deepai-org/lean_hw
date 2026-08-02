-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compile
import Loom.Hw.Compose
import Loom.Emit.MicroVerilog.RoundTrip

/-!
# D39 — declared observability: a design may keep a register off the interface

Before D39 the compiler exported **every** register as an `o_<name>` output
port. That is a defect, not a convenience: it means a Loom design
structurally cannot hold a secret. The capability engine found it — the MAC
key in `Machines/CapWalk/Engine.lean` had to be a bitstream constant rather
than a register, because "a never-written register would emit as an `o_*`
port and publish the key" (`CAPWALK_SPEC.md` deviation CE5, retired by this
file). `Loom/Hw/OUTPUTS_SPEC.md` is the decision record.

The representation is one optional field on `Design` (`Loom/Hw/Syntax.lean`):

    outputs : Option (List String) := none

`none` = every register, i.e. exactly the pre-D39 behaviour, definitionally
(`Design.exportedRegs` reduces to `d.regs`), which is why every emitted
`rtl/*.v` is byte-identical across this change. `some ns` = exactly the
named registers; everything else is **internal**.

## What this file contains

1. the decidable well-formedness check `Design.outputsOkB` — a selected name
   that is not a declared register is an error at `Design.emit`, named
   (`Loom/Hw/EmitIO.lean`, beside the D15 name-clash and D37 image checks);
2. **the theorem** (`compile_not_exported`): for `outputs = some ns`, a name
   outside `ns` occurs at no output port of `(compile d)` — neither as a port
   name nor inside a port's driver expression;
3. the same statement one level lower, over the **printed text**
   (`printed_not_exported`), via the independent parser and
   `Module.parseCheck`.

## Honesty boundary (do not let this drift)

Declared observability prevents **architectural** disclosure: the value is
at no module port, so nothing above the design boundary can read it. It
does **not** prevent physical extraction — a bitstream can be read back on
most FPGAs, and a constant or a reset value is recoverable from it. The
claim is "not exported at the interface", never "unrecoverable from the
device". A threat model that needs the latter wants key derivation from a
device secret (PUF/TRNG), which is out of scope here and is named as such
in `CAPWALK_SPEC.md` CE5.

Nothing here is read by a semantic function — not `Expr.eval`, not
`Design.cycle`, not the printer — apart from `compile`'s port list itself,
which is the point of the feature.
-/

namespace Loom.Emit.MicroVerilog

/-- The register names an emitted expression reads. Used only to *state*
D39's non-export theorem: "the register `n` occurs nowhere in the module's
port section" is stronger than "no port is called `o_n`". -/
def Expr.regReads : {w : Nat} → Expr w → List String
  | _, .lit _         => []
  | _, .reg _ n       => [n]
  | _, .memRead _ _ a => a.regReads
  | _, .and a b       => a.regReads ++ b.regReads
  | _, .or a b        => a.regReads ++ b.regReads
  | _, .xor a b       => a.regReads ++ b.regReads
  | _, .not a         => a.regReads
  | _, .add a b       => a.regReads ++ b.regReads
  | _, .sub a b       => a.regReads ++ b.regReads
  | _, .shl a b       => a.regReads ++ b.regReads
  | _, .shr a b       => a.regReads ++ b.regReads
  | _, .eq a b        => a.regReads ++ b.regReads
  | _, .ult a b       => a.regReads ++ b.regReads
  | _, .slt a b       => a.regReads ++ b.regReads
  | _, .mux c t f     => c.regReads ++ t.regReads ++ f.regReads
  | _, .slice a _ _   => a.regReads
  | _, .zext a _      => a.regReads
  | _, .sext a _      => a.regReads

/-- Every port name of a module: the D15 inputs and the D39 outputs. `clk`
and `rst` are structural and carry no design signal. -/
def Module.portNames (m : Module) : List String :=
  m.ins.map (·.name) ++ m.outs.map (·.name)

end Loom.Emit.MicroVerilog

namespace Loom.Hw

open Loom.Emit.MicroVerilog

/-! ## String-prefix injectivity (the `o_` port-name prefix) -/

/-- `String.append` is injective in its second argument. Needed because the
port name of register `n` is the string `"o_" ++ n`: distinct registers must
give distinct ports, or "no port is called `o_n`" would say nothing. -/
theorem append_right_inj {p a b : String} (h : p ++ a = p ++ b) : a = b := by
  have hd : p.toList ++ a.toList = p.toList ++ b.toList := by
    rw [← String.toList_append, ← String.toList_append, h]
  exact String.toList_injective (List.append_cancel_left hd)

theorem oPort_inj {a b : String} (h : s!"o_{a}" = s!"o_{b}") : a = b :=
  append_right_inj (p := "o_") h

/-! ## The well-formedness check (spec §2) -/

/-- The selected names that are not declared registers of `d`. Empty when
`outputs = none`. -/
def Design.outputsUndeclared (d : Design) : List String :=
  match d.outputs with
  | none    => []
  | some ns => ns.filter fun n => !(d.regs.map (·.name)).contains n

/-- **The D39 check.** `true` iff every name in the observability selection
is a declared register of `d`. `Design.emit` refuses anything else, naming
the offending selection entry: a typo in a selection would otherwise silently
*drop* a port rather than announce itself. -/
def Design.outputsOkB (d : Design) : Bool := d.outputsUndeclared.isEmpty

/-- The refusal message for one undeclared selection entry. -/
def Design.outputsError (d : Design) (n : String) : String :=
  s!"Design.emit: design '{d.name}' selects output '{n}' (D39 \
`Design.outputs`), which is not a declared register. A selection names \
REGISTERS, and each becomes the port `o_{n}`; an unrecognized name would \
silently export nothing. Fix: correct the name, or drop it from the \
selection (`Loom/Hw/OUTPUTS_SPEC.md` §2)."

/-- A human-readable D39 report line. -/
def Design.outputsReport (d : Design) : String :=
  match d.outputs with
  | none    => s!"  {d.name}: outputs=ALL ({d.regs.length} registers, pre-D39 default)"
  | some ns =>
      s!"  {d.name}: outputs=SELECTED {d.exportedRegs.length}/{d.regs.length} \
exported, {d.regs.length - d.exportedRegs.length} internal, \
selection={ns.length} names, ok={d.outputsOkB}"

/-! ## `none` is the identity (spec §1) -/

/-- The default reproduces the pre-D39 register list, definitionally. -/
theorem exportedRegs_none {d : Design} (h : d.outputs = none) :
    d.exportedRegs = d.regs := by
  simp [Design.exportedRegs, h]

/-- A selection filters the declared registers. -/
theorem exportedRegs_some {d : Design} {ns : List String}
    (h : d.outputs = some ns) :
    d.exportedRegs = d.regs.filter fun r => ns.contains r.name := by
  simp [Design.exportedRegs, h]

/-- ...hence the pre-D39 port list, definitionally. This is the statement
behind the byte-identical acceptance test: nothing downstream of `outs` can
observe that D39 happened for a design that does not use it. -/
theorem compile_outs_of_none {d : Design} (h : d.outputs = none) :
    (Compile.compile d).outs = d.regs.map fun r =>
      ({ name := s!"o_{r.name}", width := r.width,
         val := .reg r.width r.name } : OutDef) := by
  simp [Compile.compile, exportedRegs_none h]

/-- The port list, in the shape every proof below uses. -/
theorem compile_outs (d : Design) :
    (Compile.compile d).outs = d.exportedRegs.map fun r =>
      ({ name := s!"o_{r.name}", width := r.width,
         val := .reg r.width r.name } : OutDef) := rfl

/-- An exported register is a declared register: a selection can only ever
*remove* ports, never invent one. -/
theorem exportedRegs_sublist (d : Design) : d.exportedRegs.Sublist d.regs := by
  unfold Design.exportedRegs
  cases d.outputs with
  | none => exact List.Sublist.refl _
  | some ns => exact List.filter_sublist

/-- Every exported name is selected. -/
theorem mem_of_mem_exportedRegs {d : Design} {ns : List String}
    (h : d.outputs = some ns) {r : RegDecl} (hr : r ∈ d.exportedRegs) :
    r.name ∈ ns := by
  rw [exportedRegs_some h] at hr
  have := (List.mem_filter.mp hr).2
  simpa using this

/-! ## The theorem (spec §3)

For `outputs = some ns`, a register outside `ns` is **not exported**: no
output port is named after it and no output port's driver reads it. This is
the architectural non-disclosure property, and it is what lets a key live in
a register. -/

/-- **D39's theorem.** With `outputs = some ns`, a name `n ∉ ns` occurs at no
output port of the compiled module — neither as the port name `o_n` nor
inside the port's driver expression. Note it is stated for an arbitrary `n`,
not merely a declared register: nothing outside the selection is exported,
whether or not it is a register. -/
theorem compile_not_exported {d : Design} {ns : List String}
    (hsel : d.outputs = some ns) {n : String} (hn : n ∉ ns) :
    ∀ o ∈ (Compile.compile d).outs, o.name ≠ s!"o_{n}" ∧ n ∉ o.val.regReads := by
  intro o ho
  rw [compile_outs] at ho
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
  have hrn : r.name ∈ ns := mem_of_mem_exportedRegs hsel hr
  have hne : r.name ≠ n := fun h => hn (h ▸ hrn)
  refine ⟨fun h => hne (oPort_inj h), ?_⟩
  simp [Expr.regReads, Ne.symm hne]

/-- The same, at the module's whole port list: given that no *input* is
called `o_n` either (the D15 emit check keeps input names disjoint from
register names; `o_`-prefixed inputs are a caller's choice), an
unselected `n` has no port at all. -/
theorem compile_portNames_not_exported {d : Design} {ns : List String}
    (hsel : d.outputs = some ns) {n : String} (hn : n ∉ ns)
    (hin : ∀ i ∈ d.inputs, i.name ≠ s!"o_{n}") :
    s!"o_{n}" ∉ (Compile.compile d).portNames := by
  intro hmem
  rcases List.mem_append.mp hmem with h | h
  · obtain ⟨i, hi, hname⟩ := List.mem_map.mp h
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
    exact hin i0 hi0 hname
  · obtain ⟨o, ho, hname⟩ := List.mem_map.mp h
    exact (compile_not_exported hsel hn o ho).1 hname

/-! ## Composition (spec §4)

What each D16 combinator does to a selection, stated and proved. The rule
the three share: **composition may not publish an internal register.** -/

/-- `contains` survives prefixing on both sides (`p ++ ·` is injective). -/
theorem contains_map_prefix (p n : String) : ∀ ns : List String,
    (ns.map (p ++ ·)).contains (p ++ n) = ns.contains n
  | [] => rfl
  | a :: t => by
      have hb : ((p ++ n) == (p ++ a)) = (n == a) := by
        by_cases h : n = a
        · simp [h]
        · have hne : ¬ (p ++ n) = (p ++ a) := fun he => h (append_right_inj he)
          simp [h, hne]
      simp only [List.map_cons, List.contains_cons, hb, contains_map_prefix p n t]

/-- The register-list half of `prefixed`, as a list lemma. -/
private theorem filter_map_prefix (p : String) (ns : List String) :
    ∀ rs : List RegDecl,
      (rs.map fun r => ({ r with name := p ++ r.name } : RegDecl)).filter
          (fun r => (ns.map (p ++ ·)).contains r.name)
        = (rs.filter fun r => ns.contains r.name).map
            fun r => ({ r with name := p ++ r.name } : RegDecl)
  | [] => rfl
  | r :: t => by
      have ih := filter_map_prefix p ns t
      simp only [List.map_cons, List.filter_cons, contains_map_prefix, ih]
      cases ns.contains r.name <;> simp

/-- **`prefixed` renames the selection with the registers.** Instantiating a
design under a namespace exports the same registers under their instance
names — an internal register of `d` is internal in every instance of `d`. -/
theorem prefixed_exportedRegs (p : String) (d : Design) :
    (d.prefixed p).exportedRegs =
      d.exportedRegs.map fun r => ({ r with name := p ++ r.name } : RegDecl) := by
  cases h : d.outputs with
  | none =>
      have hp : (d.prefixed p).outputs = none := by simp [Design.prefixed, h]
      rw [exportedRegs_none hp, exportedRegs_none h]
      rfl
  | some ns =>
      have hp : (d.prefixed p).outputs = some (ns.map (p ++ ·)) := by
        simp [Design.prefixed, h]
      rw [exportedRegs_some hp, exportedRegs_some h]
      exact filter_map_prefix p ns d.regs

/-- Filtering a design's own registers by its *exported names* is the
selection itself — in both the `none` and the `some` case. -/
theorem filter_exportedNames (d : Design) :
    d.regs.filter (fun r => d.exportedNames.contains r.name) = d.exportedRegs := by
  cases hout : d.outputs with
  | none =>
      rw [exportedRegs_none hout]
      apply List.filter_eq_self.mpr
      intro r hr
      have hmem : r.name ∈ d.exportedNames := by
        simp only [Design.exportedNames, exportedRegs_none hout]
        exact List.mem_map_of_mem hr
      simp [hmem]
  | some ns =>
      rw [exportedRegs_some hout]
      apply List.filter_congr
      intro r hr
      simp only [List.contains_eq_mem, decide_eq_decide]
      constructor
      · intro h
        obtain ⟨r', hr', hname⟩ := List.mem_map.mp h
        have := mem_of_mem_exportedRegs hout hr'
        rwa [hname] at this
      · intro h
        have hmem : r ∈ d.exportedRegs := by
          rw [exportedRegs_some hout]
          exact List.mem_filter.mpr ⟨hr, by simpa using h⟩
        simpa [Design.exportedNames] using List.mem_map_of_mem hmem

/-- **`par` concatenates.** With the two parts' selections not naming each
other's registers — which `parOkB`'s name disjointness gives, and which is
vacuous when either part exports everything — the composite exports exactly
the concatenation. -/
theorem par_exportedRegs (a b : Design)
    (hab : ∀ r ∈ a.regs, r.name ∈ b.exportedNames → r.name ∈ a.exportedNames)
    (hba : ∀ r ∈ b.regs, r.name ∈ a.exportedNames → r.name ∈ b.exportedNames) :
    (a.par b).exportedRegs = a.exportedRegs ++ b.exportedRegs := by
  have key : (a.regs ++ b.regs).filter
        (fun r => (a.exportedNames ++ b.exportedNames).contains r.name)
      = a.exportedRegs ++ b.exportedRegs := by
    rw [List.filter_append]
    congr 1
    · rw [← filter_exportedNames a]
      apply List.filter_congr
      intro r hr
      simp only [List.contains_eq_mem, decide_eq_decide, List.mem_append]
      exact ⟨fun h => h.elim id (hab r hr), fun h => Or.inl h⟩
    · rw [← filter_exportedNames b]
      apply List.filter_congr
      intro r hr
      simp only [List.contains_eq_mem, decide_eq_decide, List.mem_append]
      exact ⟨fun h => h.elim (hba r hr) id, fun h => Or.inr h⟩
  cases ha : a.outputs with
  | none =>
      cases hb : b.outputs with
      | none =>
          have hp : (a.par b).outputs = none := by simp [Design.par, ha, hb]
          rw [exportedRegs_none hp, exportedRegs_none ha, exportedRegs_none hb]
          rfl
      | some nb =>
          have hp : (a.par b).outputs =
              some (a.exportedNames ++ b.exportedNames) := by
            simp [Design.par, ha, hb]
          rw [exportedRegs_some hp]; exact key
  | some na =>
      have hp : (a.par b).outputs =
          some (a.exportedNames ++ b.exportedNames) := by
        cases hb : b.outputs <;> simp [Design.par, ha, hb]
      rw [exportedRegs_some hp]; exact key

/-- The safety half of `par`, with **no** hypotheses: composition cannot
publish a register that neither part exported. -/
theorem par_exportedNames_subset (a b : Design) :
    ∀ r ∈ (a.par b).exportedRegs,
      r.name ∈ a.exportedNames ++ b.exportedNames := by
  intro r hr
  cases ha : a.outputs with
  | none =>
      cases hb : b.outputs with
      | none =>
          have hp : (a.par b).outputs = none := by simp [Design.par, ha, hb]
          rw [exportedRegs_none hp] at hr
          have : r ∈ a.regs ++ b.regs := hr
          simp only [Design.exportedNames, exportedRegs_none ha,
            exportedRegs_none hb, ← List.map_append]
          exact List.mem_map_of_mem this
      | some nb =>
          have hp : (a.par b).outputs =
              some (a.exportedNames ++ b.exportedNames) := by
            simp [Design.par, ha, hb]
          rw [exportedRegs_some hp] at hr
          simpa using (List.mem_filter.mp hr).2
  | some na =>
      have hp : (a.par b).outputs =
          some (a.exportedNames ++ b.exportedNames) := by
        cases hb : b.outputs <;> simp [Design.par, ha, hb]
      rw [exportedRegs_some hp] at hr
      simpa using (List.mem_filter.mp hr).2

/-- **`connect` leaves the selection alone.** Wiring an input from a
register cannot resurrect a dropped output: `connect` touches inputs and
rule bodies only. -/
theorem connect_exportedRegs (d : Design)
    (wire : (n : String) → (w : Nat) → Option (Expr w)) :
    (d.connect wire).exportedRegs = d.exportedRegs := rfl

/-- ...hence the wired design's ports are exactly the unwired design's. -/
theorem connect_outs (d : Design)
    (wire : (n : String) → (w : Nat) → Option (Expr w)) :
    (Compile.compile (d.connect wire)).outs = (Compile.compile d).outs := rfl

/-! ## The theorem, over the printed text

`compile_not_exported` is about the compiler's data structure. The emitted
artifact is *text*, and the printer is not on the trusted path: the
independent parser reads the text back and `Module.parseCheck` (run over
every `rtl/*.v` by `lake exe rtlroundtrip`, in `scripts/ci.sh`) decides
whether the text determines the module. Given that verdict, the non-export
property is a property of the file. -/

/-- **D39's theorem at the text level.** If the emitted text round-trips
(`parseCheck`, the per-artifact CI gate), then the module an independent
parser recovers from that text exports no unselected name either. -/
theorem printed_not_exported {d : Design} {ns : List String}
    (hsel : d.outputs = some ns) {n : String} (hn : n ∉ ns)
    (hrt : (Compile.compile d).parseCheck = true) :
    ∃ m, Parse.parse (Print.print (Compile.compile d)) = some m ∧
      ∀ o ∈ m.outs, o.name ≠ s!"o_{n}" ∧ n ∉ o.val.regReads := by
  obtain ⟨m, hparse, hmatch⟩ := Module.parseCheck_sound hrt
  refine ⟨m, hparse, ?_⟩
  intro o ho
  exact compile_not_exported hsel hn o (hmatch.outs ▸ ho)

end Loom.Hw
