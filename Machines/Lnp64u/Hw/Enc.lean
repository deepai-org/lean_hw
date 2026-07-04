-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Loom.Hw.Semantics
import Machines.Lnp64u.Manifest

/-!
# LNP64-µ hardware encoding kit (task 1.11)

The R-MC contract's vocabulary, per `Hw/DESIGN.md` (binding):

* **Register names** — one EDSL register per scalar spec field, `Fin`-indexed
  families as numbered names (`d2_reg5`). The name helpers here are the only
  place the strings are spelled.
* **Bit packings** — `encKind`/`decKind` (32-bit kind word: bit 0 tag; mem:
  base `[12:1]`, len `[25:13]`, perms `[28:26]` r,w,x; gate: gid `[2:1]`),
  `encRef`/`decRef` (14-bit CapRef: gen `[7:0]`, slot `[11:8]`, dom `[13:12]`),
  `encRegion`/`decRegion` (42-bit region: perms `[2:0]`, len `[15:3]`,
  base `[27:16]`, backing `[41:28]`), `encRun` (00 running, 01 halted,
  10 blocked + gate in `run_g`).
* **Expr combinators** — `muxFin` selection trees, `orAll`/`andAll`/`seqAll`,
  `field`/`insertField` packed-field access. The `Option` idiom is a 1-bit
  `_v` register plus payload registers; `abs` decodes `_v = 1` as `some`.
* **`regDecls`/`memDecl`** — the full register file and the 4096×32 RAM,
  reset values computed from `m.initState` (the one meaning of "reset").
* **`abs`** — decode the register file back to `MachineState`. Total:
  garbage encodings take canonical fallbacks (`run = 11 ↦ .running`; out-of-
  range never occurs since every `Fin`-carrying field's width is exact).

Hidden state (ignored by `abs`, reported for the R-MC invariant): the
per-domain refill counters `d{d}_rctr`, which track `cycle % periodP d`
because the Expr language has no modulo, and the `cap_revoke` mark engine
`rv_j/rv_v/rv_r` (one pointer-doubling node per machine slot, iterated in
the in-flight countdown cycles — see `Hw/SysOps.lean`).
-/

namespace Machines.Lnp64u.Hw

open Loom.Hw

/-! ## Register names (DESIGN.md state-encoding table) -/

def dreg (d : DomainId) (r : RegId) : String := s!"d{d.val}_reg{r.val}"
def dpc (d : DomainId) : String := s!"d{d.val}_pc"
def dcapV (d : DomainId) (s : Slot) : String := s!"d{d.val}_cap{s.val}_v"
def dcapKind (d : DomainId) (s : Slot) : String := s!"d{d.val}_cap{s.val}_kind"
def dcapLinV (d : DomainId) (s : Slot) : String := s!"d{d.val}_cap{s.val}_lin_v"
def dcapLin (d : DomainId) (s : Slot) : String := s!"d{d.val}_cap{s.val}_lin"
def dgen (d : DomainId) (s : Slot) : String := s!"d{d.val}_gen{s.val}"
def dcellV (d : DomainId) (l : LineageId) : String := s!"d{d.val}_cell{l.val}_v"
def dcellPar (d : DomainId) (l : LineageId) : String := s!"d{d.val}_cell{l.val}_par"
def drgnV (d : DomainId) (r : RegionId) : String := s!"d{d.val}_rgn{r.val}_v"
def drgn (d : DomainId) (r : RegionId) : String := s!"d{d.val}_rgn{r.val}"
def drun (d : DomainId) : String := s!"d{d.val}_run"
def drunG (d : DomainId) : String := s!"d{d.val}_run_g"
def dsrvV (d : DomainId) : String := s!"d{d.val}_srv_v"
def dsrv (d : DomainId) : String := s!"d{d.val}_srv"
def dcause (d : DomainId) : String := s!"d{d.val}_cause"
def dbudget (d : DomainId) : String := s!"d{d.val}_budget"
def dmaxdon (d : DomainId) : String := s!"d{d.val}_maxdon"
/-- Hidden: refill counter tracking `cycle % periodP d` (no mod in `Expr`).
Not part of the state-encoding table; `abs` ignores it. -/
def drctr (d : DomainId) : String := s!"d{d.val}_rctr"

/-- A machine-wide slot index: node `i` is slot `i % 16` of domain `i / 16`
(the `cap_revoke` mark engine's vertex set). -/
abbrev NodeId := Fin (numDomains * numSlots)

def nDom (i : NodeId) : DomainId :=
  ⟨i.val / 16, by show i.val / 16 < 4; have h : i.val < 64 := i.isLt; omega⟩
def nSlot (i : NodeId) : Slot :=
  ⟨i.val % 16, by show i.val % 16 < 16; omega⟩

/-- Hidden `cap_revoke` mark-engine registers (pointer doubling): current
jump target (6-bit node), chain-valid, reached-root. `abs` ignores them. -/
def rvJ (i : NodeId) : String := s!"rv_j{i.val}"
def rvV (i : NodeId) : String := s!"rv_v{i.val}"
def rvR (i : NodeId) : String := s!"rv_r{i.val}"

def gcallee (g : GateId) : String := s!"g{g.val}_callee"
def gentry (g : GateId) : String := s!"g{g.val}_entry"
def gactV (g : GateId) : String := s!"g{g.val}_act_v"
def gcaller (g : GateId) : String := s!"g{g.val}_caller"
def gcallerRd (g : GateId) : String := s!"g{g.val}_callerrd"
def gsreg (g : GateId) (r : RegId) : String := s!"g{g.val}_sreg{r.val}"
def gspc (g : GateId) : String := s!"g{g.val}_spc"
def gssrvV (g : GateId) : String := s!"g{g.val}_ssrv_v"
def gssrv (g : GateId) : String := s!"g{g.val}_ssrv"
def gdepth (g : GateId) : String := s!"g{g.val}_depth"
def gdon (g : GateId) : String := s!"g{g.val}_don"

/-! ## Bit packings (spec value ↔ bits; used for reset, literals, and `abs`) -/

/-- Exact-width `Fin` from a bit vector (every `Fin`-carrying field's width
is exact at µ parameters, so decode never truncates). -/
def finOfBv {w n : Nat} (h : 2 ^ w = n) (x : BitVec w) : Fin n :=
  ⟨x.toNat, h ▸ x.isLt⟩

def encPerms (p : Perms) : BitVec 3 :=
  (if p.r then 1 else 0) ||| ((if p.w then 1 else 0) <<< 1) |||
  ((if p.x then 1 else 0) <<< 2)

def decPerms (b : BitVec 3) : Perms :=
  { r := b.getLsbD 0, w := b.getLsbD 1, x := b.getLsbD 2 }

/-- CapRef, 14 bits: gen `[7:0]`, slot `[11:8]`, dom `[13:12]`. -/
def encRef (c : CapRef) : BitVec 14 :=
  (c.gen.setWidth 14) ||| (BitVec.ofNat 14 c.slot.val <<< 8) |||
  (BitVec.ofNat 14 c.dom.val <<< 12)

def decRef (b : BitVec 14) : CapRef where
  dom := finOfBv (by decide) (b.extractLsb' 12 2)
  slot := finOfBv (by decide) (b.extractLsb' 8 4)
  gen := b.extractLsb' 0 8

/-- Kind word, 32 bits: bit 0 tag (0 mem, 1 gate); mem: base `[12:1]`,
len `[25:13]`, perms `[28:26]`; gate: gid `[2:1]`. -/
def encKind : CapKind → BitVec 32
  | .mem base len perms =>
      (base.setWidth 32 <<< 1) ||| (len.setWidth 32 <<< 13) |||
      ((encPerms perms).setWidth 32 <<< 26)
  | .gate g => 1 ||| (BitVec.ofNat 32 g.val <<< 1)

def decKind (w : BitVec 32) : CapKind :=
  if w.getLsbD 0 then .gate (finOfBv (by decide) (w.extractLsb' 1 2))
  else .mem (w.extractLsb' 1 12) (w.extractLsb' 13 13)
        (decPerms (w.extractLsb' 26 3))

/-- Region, 42 bits: perms `[2:0]`, len `[15:3]`, base `[27:16]`,
backing `[41:28]`. -/
def encRegion (rg : Region) : BitVec 42 :=
  (encPerms rg.perms).setWidth 42 ||| (rg.len.setWidth 42 <<< 3) |||
  (rg.base.setWidth 42 <<< 16) ||| ((encRef rg.backing).setWidth 42 <<< 28)

def decRegion (b : BitVec 42) : Region where
  base := b.extractLsb' 16 12
  len := b.extractLsb' 3 13
  perms := decPerms (b.extractLsb' 0 3)
  backing := decRef (b.extractLsb' 28 14)

def encRun : RunState → BitVec 2
  | .running => 0
  | .halted => 1
  | .blocked _ => 2

def encRunG : RunState → BitVec 2
  | .blocked g => BitVec.ofNat 2 g.val
  | _ => 0

/-- Canonical-fallback decode: `11 ↦ .running`. -/
def decRun (b g : BitVec 2) : RunState :=
  if b = 0 then .running
  else if b = 1 then .halted
  else if b = 2 then .blocked (finOfBv (by decide) g)
  else .running

/-! ## Expr-level combinators -/

/-- `n`-way selection tree: pick `f i` where `idx = i` (mux chain; the
fallback `0` arm is unreachable when `2 ^ iw = n`). -/
def muxFin {n iw w : Nat} (f : Fin n → Expr w) (idx : Expr iw) : Expr w :=
  (List.finRange n).foldr
    (fun i acc => .mux (.eq idx (.lit (BitVec.ofNat iw i.val))) (f i) acc)
    (.lit 0)

def orAll : List (Expr 1) → Expr 1
  | [] => .lit 0
  | [e] => e
  | e :: es => .or e (orAll es)

def andAll : List (Expr 1) → Expr 1
  | [] => .lit 1
  | [e] => e
  | e :: es => .and e (andAll es)

def seqAll (l : List Act) : Act := l.foldr .seq .skip

/-- Extract a packed field (`slice`, named for symmetry with `insertField`). -/
def field {w : Nat} (e : Expr w) (lo width : Nat) : Expr width :=
  .slice e lo width

/-- Insert `v` at bit `lo` of `base` (mask-and-or; the packed-field write). -/
def insertField {w fw : Nat} (base : Expr w) (lo : Nat) (v : Expr fw) : Expr w :=
  .or (.and base (.lit (~~~(BitVec.ofNat w (2 ^ fw - 1) <<< lo))))
      (.shl (.zext v w) (.lit (BitVec.ofNat w lo)))

/-! ## Register declarations (reset = `m.initState`) -/

def domDecls (m : Manifest) (d : DomainId) : List RegDecl :=
  let ds := m.initState.doms d
  ((List.finRange numRegs).map fun r => ⟨dreg d r, 32, ds.regs r⟩)
  ++ [⟨dpc d, 12, ds.pc⟩]
  ++ ((List.finRange numSlots).flatMap fun s =>
      let e := ds.caps s
      [⟨dcapV d s, 1, if e.isSome then 1 else 0⟩,
       ⟨dcapKind d s, 32, (e.map fun c => encKind c.kind).getD 0⟩,
       ⟨dcapLinV d s, 1, if (e.bind (·.lineage)).isSome then 1 else 0⟩,
       ⟨dcapLin d s, 4,
        ((e.bind (·.lineage)).map fun l => BitVec.ofNat 4 l.val).getD 0⟩,
       ⟨dgen d s, 8, ds.slotGen s⟩])
  ++ ((List.finRange numLineage).flatMap fun l =>
      [⟨dcellV d l, 1, if (ds.lineage l).isSome then 1 else 0⟩,
       ⟨dcellPar d l, 14, ((ds.lineage l).map fun c => encRef c.parent).getD 0⟩])
  ++ ((List.finRange numRegions).flatMap fun r =>
      [⟨drgnV d r, 1, if (ds.regions r).isSome then 1 else 0⟩,
       ⟨drgn d r, 42, ((ds.regions r).map encRegion).getD 0⟩])
  ++ [⟨drun d, 2, encRun ds.run⟩,
      ⟨drunG d, 2, encRunG ds.run⟩,
      ⟨dsrvV d, 1, if ds.serving.isSome then 1 else 0⟩,
      ⟨dsrv d, 2, (ds.serving.map fun g => BitVec.ofNat 2 g.val).getD 0⟩,
      ⟨dcause d, 32, ds.cause⟩,
      ⟨dbudget d, 32, BitVec.ofNat 32 ds.budget⟩,
      ⟨dmaxdon d, 32, BitVec.ofNat 32 ds.maxDonation⟩,
      -- hidden refill counter (see module docstring)
      ⟨drctr d, 32, BitVec.ofNat 32 (m.initState.cycle.toNat % (m.doms d).periodP)⟩]

def gateDecls (m : Manifest) (g : GateId) : List RegDecl :=
  let gs := m.initState.gates g
  let a := gs.act
  [⟨gcallee g, 2, BitVec.ofNat 2 gs.config.callee.val⟩,
   ⟨gentry g, 12, gs.config.entry⟩,
   ⟨gactV g, 1, if a.isSome then 1 else 0⟩,
   ⟨gcaller g, 2, (a.map fun x => BitVec.ofNat 2 x.caller.val).getD 0⟩,
   ⟨gcallerRd g, 3, (a.map fun x => BitVec.ofNat 3 x.callerRd.val).getD 0⟩]
  ++ ((List.finRange numRegs).map fun r =>
      ⟨gsreg g r, 32, (a.map fun x => x.savedRegs r).getD 0⟩)
  ++ [⟨gspc g, 12, (a.map (·.savedPc)).getD 0⟩,
      ⟨gssrvV g, 1, if (a.bind (·.savedServing)).isSome then 1 else 0⟩,
      ⟨gssrv g, 2,
       ((a.bind (·.savedServing)).map fun x => BitVec.ofNat 2 x.val).getD 0⟩,
      ⟨gdepth g, 3, (a.map fun x => BitVec.ofNat 3 x.depth).getD 0⟩,
      ⟨gdon g, 32, (a.map fun x => BitVec.ofNat 32 x.donated).getD 0⟩]

def globalDecls (m : Manifest) : List RegDecl :=
  let j := m.initState.mover
  let fl := m.initState.inflight
  [⟨"mov_v", 1, if j.isSome then 1 else 0⟩,
   ⟨"mov_src", 14, (j.map fun x => encRef x.src).getD 0⟩,
   ⟨"mov_dst", 14, (j.map fun x => encRef x.dst).getD 0⟩,
   ⟨"mov_srccur", 12, (j.map (·.srcCur)).getD 0⟩,
   ⟨"mov_dstcur", 12, (j.map (·.dstCur)).getD 0⟩,
   ⟨"mov_rem", 13, (j.map fun x => BitVec.ofNat 13 x.remaining).getD 0⟩,
   ⟨"mov_owner", 2, (j.map fun x => BitVec.ofNat 2 x.owner.val).getD 0⟩,
   ⟨"mov_status", 12, (j.map (·.statusAddr)).getD 0⟩,
   ⟨"if_v", 1, if fl.isSome then 1 else 0⟩,
   ⟨"if_dom", 2, (fl.map fun x => BitVec.ofNat 2 x.dom.val).getD 0⟩,
   ⟨"if_word", 32, (fl.map (·.word)).getD 0⟩,
   ⟨"if_cl", 8, (fl.map fun x => BitVec.ofNat 8 x.cyclesLeft).getD 0⟩,
   ⟨"cycle", 32, m.initState.cycle⟩]

/-- Every register of the design (state-encoding table + hidden counters),
reset from `m.initState`. -/
def regDecls (m : Manifest) : List RegDecl :=
  ((List.finRange numDomains).flatMap (domDecls m))
  ++ ((List.finRange numGates).flatMap (gateDecls m))
  ++ globalDecls m
  -- hidden cap_revoke mark engine (see module docstring); abs ignores these
  ++ ((List.finRange (numDomains * numSlots)).flatMap fun i =>
      [⟨rvJ i, 6, 0⟩, ⟨rvV i, 1, 0⟩, ⟨rvR i, 1, 0⟩])

/-- The 4096×32 physical memory, initialized from the manifest's boot image
(`initState.mem = m.rom`). -/
def memDecl (m : Manifest) : MemDecl where
  name := "mem"
  addrWidth := 12
  dataWidth := 32
  init := fun a => m.initState.mem (BitVec.ofNat 12 a)

/-! ## The abstraction function (R-MC contract) -/

def absDom (σ : Loom.Hw.St) (d : DomainId) : DomainState where
  regs := fun r => σ.regs (dreg d r) 32
  pc := σ.regs (dpc d) 12
  caps := fun s =>
    if σ.regs (dcapV d s) 1 = 1 then
      some { kind := decKind (σ.regs (dcapKind d s) 32)
             lineage :=
               if σ.regs (dcapLinV d s) 1 = 1 then
                 some (finOfBv (by decide) (σ.regs (dcapLin d s) 4))
               else none }
    else none
  slotGen := fun s => σ.regs (dgen d s) 8
  lineage := fun l =>
    if σ.regs (dcellV d l) 1 = 1 then
      some ⟨decRef (σ.regs (dcellPar d l) 14)⟩
    else none
  regions := fun r =>
    if σ.regs (drgnV d r) 1 = 1 then some (decRegion (σ.regs (drgn d r) 42))
    else none
  run := decRun (σ.regs (drun d) 2) (σ.regs (drunG d) 2)
  serving :=
    if σ.regs (dsrvV d) 1 = 1 then some (finOfBv (by decide) (σ.regs (dsrv d) 2))
    else none
  cause := σ.regs (dcause d) 32
  budget := (σ.regs (dbudget d) 32).toNat
  maxDonation := (σ.regs (dmaxdon d) 32).toNat

def absGate (σ : Loom.Hw.St) (g : GateId) : GateState where
  config :=
    { callee := finOfBv (by decide) (σ.regs (gcallee g) 2)
      entry := σ.regs (gentry g) 12 }
  act :=
    if σ.regs (gactV g) 1 = 1 then
      some { caller := finOfBv (by decide) (σ.regs (gcaller g) 2)
             callerRd := finOfBv (by decide) (σ.regs (gcallerRd g) 3)
             savedRegs := fun r => σ.regs (gsreg g r) 32
             savedPc := σ.regs (gspc g) 12
             savedServing :=
               if σ.regs (gssrvV g) 1 = 1 then
                 some (finOfBv (by decide) (σ.regs (gssrv g) 2))
               else none
             depth := (σ.regs (gdepth g) 3).toNat
             donated := (σ.regs (gdon g) 32).toNat }
    else none

def absMover (σ : Loom.Hw.St) : Option MoverJob :=
  if σ.regs "mov_v" 1 = 1 then
    some { owner := finOfBv (by decide) (σ.regs "mov_owner" 2)
           src := decRef (σ.regs "mov_src" 14)
           dst := decRef (σ.regs "mov_dst" 14)
           srcCur := σ.regs "mov_srccur" 12
           dstCur := σ.regs "mov_dstcur" 12
           remaining := (σ.regs "mov_rem" 13).toNat
           statusAddr := σ.regs "mov_status" 12 }
  else none

def absInflight (σ : Loom.Hw.St) : Option InFlight :=
  if σ.regs "if_v" 1 = 1 then
    some { dom := finOfBv (by decide) (σ.regs "if_dom" 2)
           word := σ.regs "if_word" 32
           cyclesLeft := (σ.regs "if_cl" 8).toNat }
  else none

/-- Decode the register file back to the spec state (total; the R-MC
abstraction). -/
def abs (σ : Loom.Hw.St) : MachineState where
  cycle := σ.regs "cycle" 32  -- spec cycle is the hardware register, verbatim
  mem := fun a => σ.mems "mem" a.toNat 32
  doms := absDom σ
  gates := absGate σ
  mover := absMover σ
  inflight := absInflight σ

end Machines.Lnp64u.Hw
