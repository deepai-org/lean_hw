import Batteries.Data.List.Basic
import Mathlib.Data.Sigma.Basic
import Loom.Emit.MicroVerilog.Print
import Loom.Emit.MicroVerilog.Parse

/-!
# µVerilog round-trip (task 2.3)

Closes the text-level trust gap: the emission theorems talk about a
`Module` AST, and `lake exe emit` writes `Print.print m` to disk — so the
pretty-printer would be trusted unless parsing the *text* provably
recovers the module. This file provides the decidable-checker form of
that guarantee:

* `Module.Matches m' m` — everything the printed text pins down:
  syntactic equality of the name, registers and outputs, and per-memory
  equality of every field *including the full printed init image on
  `[0, 2^addrWidth)`*. The only thing not covered is each memory's `init`
  function at addresses `≥ 2^addrWidth`: the text does not (and cannot)
  mention those, and `Expr.eval`/`Module.reset` observed through reads
  never reach them, since read addresses are `BitVec addrWidth` values.
* `Module.parseCheck m : Bool` — runs `Parse.parse (Print.print m)` and
  compares the result against `m` up to `Matches`. Fully decidable (no
  `native_decide` anywhere): a *concrete* emitted module gets its
  text-level theorem by kernel evaluation.
* `Module.parseCheck_sound` — `parseCheck m = true` really does yield
  `parse (print m) = some m'` with `m'.Matches m`.

The universally-quantified `∀ m, PrintWF m → parse (print m) = …` form
(round-trip for *arbitrary* modules) is not proven here; each concrete
emitted artifact (Acc8 today, LNP64-µ when its core lands) discharges
`parseCheck` instead, which closes the same trust gap for everything
actually emitted. See `Machines/Acc8/EmitRoundTrip.lean` for the Acc8
instance.
-/

namespace Loom.Emit.MicroVerilog

deriving instance DecidableEq for Expr
deriving instance DecidableEq for RegDef
deriving instance DecidableEq for OutDef

/-- Pointwise conjunction of a Boolean test over two lists (false on a
length mismatch). -/
def listAll2 {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listAll2 f as bs
  | _, _ => false

theorem listAll2_sound {α β : Type} {R : α → β → Prop} (f : α → β → Bool)
    (hf : ∀ a b, f a b = true → R a b) :
    ∀ {as : List α} {bs : List β}, listAll2 f as bs = true → List.Forall₂ R as bs
  | [], [], _ => .nil
  | a :: as, b :: bs, h => by
    simp only [listAll2, Bool.and_eq_true] at h
    exact .cons (hf a b h.1) (listAll2_sound f hf h.2)
  | [], _ :: _, h => by simp [listAll2] at h
  | _ :: _, [], h => by simp [listAll2] at h

/-- Agreement of two memory definitions on everything the printed text
determines: all scalar fields, the port expressions (heterogeneously,
with their widths), and the init image on the whole address space
`[0, 2^addrWidth)`. `init` beyond the address space is unprintable and
unreadable (read addresses are `BitVec addrWidth`), hence unconstrained. -/
structure MemDef.Matches (a b : MemDef) : Prop where
  name      : a.name = b.name
  addrWidth : a.addrWidth = b.addrWidth
  dataWidth : a.dataWidth = b.dataWidth
  wrEn      : a.wrEn = b.wrEn
  wrAddr    : HEq a.wrAddr b.wrAddr
  wrData    : HEq a.wrData b.wrData
  init      : ∀ i, i < 2 ^ a.addrWidth → (a.init i).toNat = (b.init i).toNat

/-- Decidable form of `MemDef.Matches` (width-indexed expressions are
compared as `Sigma Expr` values, which also decides the width fields). -/
def MemDef.matchesb (a b : MemDef) : Bool :=
  decide (a.name = b.name) &&
  decide (a.wrEn = b.wrEn) &&
  decide ((⟨a.addrWidth, a.wrAddr⟩ : Sigma Expr) = ⟨b.addrWidth, b.wrAddr⟩) &&
  decide ((⟨a.dataWidth, a.wrData⟩ : Sigma Expr) = ⟨b.dataWidth, b.wrData⟩) &&
  decide (∀ i, i < 2 ^ a.addrWidth → (a.init i).toNat = (b.init i).toNat)

theorem MemDef.matchesb_sound {a b : MemDef} (h : a.matchesb b = true) :
    a.Matches b := by
  simp only [matchesb, Bool.and_eq_true, decide_eq_true_eq, Sigma.mk.injEq] at h
  obtain ⟨⟨⟨⟨hn, hen⟩, haw, had⟩, hdw, hdt⟩, hinit⟩ := h
  exact ⟨hn, haw, hdw, hen, had, hdt, hinit⟩

/-- Agreement of two modules on everything the printed text determines:
syntactic equality except for memory init functions beyond the printed
(= complete, addressable) image. -/
structure Module.Matches (a b : Module) : Prop where
  name : a.name = b.name
  regs : a.regs = b.regs
  outs : a.outs = b.outs
  mems : List.Forall₂ MemDef.Matches a.mems b.mems

/-- Decidable form of `Module.Matches`. -/
def Module.matchesb (a b : Module) : Bool :=
  decide (a.name = b.name) &&
  decide (a.regs = b.regs) &&
  decide (a.outs = b.outs) &&
  listAll2 MemDef.matchesb a.mems b.mems

theorem Module.matchesb_sound {a b : Module} (h : a.matchesb b = true) :
    a.Matches b := by
  simp only [matchesb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hr⟩, ho⟩, hm⟩ := h
  exact ⟨hn, hr, ho, listAll2_sound _ (fun _ _ => MemDef.matchesb_sound) hm⟩

/-- The round-trip checker: print the module, parse the text back, and
compare. `true` means the emitted TEXT determines the module (up to
`Matches`), so nothing about the pretty-printer needs to be trusted for
this module. -/
def Module.parseCheck (m : Module) : Bool :=
  match Parse.parse (Print.print m) with
  | some m' => Module.matchesb m' m
  | none => false

/-- Soundness of the checker: a `true` verdict yields the round-trip
theorem for this module — parsing the exact printed text succeeds and
recovers the module up to `Matches`. -/
theorem Module.parseCheck_sound {m : Module} (h : m.parseCheck = true) :
    ∃ m', Parse.parse (Print.print m) = some m' ∧ m'.Matches m := by
  unfold parseCheck at h
  split at h
  · next m' heq => exact ⟨m', heq, Module.matchesb_sound h⟩
  · exact absurd h (by simp)

/-! ## A machine-free kernel-checked instance

A small module exercising every RHS production the printer has (literal,
reg, memRead, binops, comparisons, `$signed`, mux, not, slice, zext,
widening sext, plus a memory with its full init image). Its round trip is
checked by `decide`, i.e. by kernel evaluation of the printer, the
parser, and the comparison — no compiled code, no `native_decide`. -/

private def demoMem : MemDef where
  name      := "m"
  addrWidth := 2
  dataWidth := 8
  init      := fun a => BitVec.ofNat 8 (3 * a + 1)
  wrEn      := .eq (.reg 4 "r") (.lit 5#4)
  wrAddr    := .slice (.reg 4 "r") 1 2
  wrData    := .mux (.ult (.reg 4 "r") (.lit 2#4))
                    (.memRead 8 "m" (.lit 0#2))
                    (.sext (.reg 4 "r") 8)

private def demo : Module where
  name := "demo"
  regs := [⟨"r", 4, 9#4,
            .add (.reg 4 "r")
                 (.zext (.slt (.not (.reg 4 "r")) (.sub (.reg 4 "r") (.lit 1#4))) 4)⟩,
           ⟨"s", 4, 0#4,
            .shr (.xor (.or (.reg 4 "s") (.reg 4 "r")) (.lit 3#4))
                 (.shl (.reg 4 "s") (.reg 4 "r"))⟩]
  mems := [demoMem]
  outs := [⟨"o", 4, .reg 4 "r"⟩,
           ⟨"p", 8, .memRead 8 "m" (.slice (.reg 4 "r") 0 2)⟩]

set_option maxRecDepth 10000 in
example : demo.parseCheck = true := by decide +kernel

end Loom.Emit.MicroVerilog
