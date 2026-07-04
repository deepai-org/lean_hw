-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Hw.BaseOps

/-!
# LNP64-µ core: the 11 system-op circuits (task 1.11, system half)

Each opcode's `exec` (Isa/System.lean) is a *sequential* SpecM program; the
circuit computes the composite end-of-exec state combinationally. All EDSL
reads are pre-cycle (D9), so every intermediate value a later kernel step
would read is re-derived as an `Expr` over the pre-cycle state:

* **errno ladders** — each op is a list of fail-condition `Check`s in the
  spec's raise order; the ladder retires `-errno` into `rd` (pc advanced),
  `Fault`s go domain-fatal through `haltAct` (pc *not* advanced), and the
  ok-path `Act` runs the composite kernel writes.
* **transfer/derive** — `freeSlot`/`freeCell` priority encoders,
  `installDerived`/`transferCap` as guarded per-slot/per-cell writes, the
  machine-wide reparent pass as per-cell compare-muxes.
* **`cap_revoke`'s marks fixpoint** — the spec's 64-iteration `markStep`
  fold equals the reachability closure of "parent edge, live-gen, ending at
  root". A naive 64× combinational unroll has no subexpression sharing in
  `Expr` and explodes; instead a **pointer-doubling engine** in hidden
  registers (`rv_j/rv_v/rv_r`, one node per machine slot) initializes at
  issue and does one doubling round per in-flight countdown cycle —
  `⌈log₂ 64⌉ + 1 = 7` rounds reach the closure, and `cap_revoke`'s WCET
  (24 cycles) provides 23. Cap state cannot change while the instruction is
  in flight (only retirements mutate cap tables and only one instruction is
  in flight), so the registers hold `marks` of the retirement state.
* **sweeps** — `sweepRegions`/`sweepMover` need *post-op* liveness. On
  reachable states every valid region's backing and every live Mover job's
  src/dst are live (kills always sweep), so post-liveness reduces to "not
  killed by this op" — the per-op `killed` predicates below. (Recorded as a
  reachability-dependent simplification; the Phase-3 R-MC proof carries the
  corresponding invariant.)

The Mover-phase composite (`Step.moverPhase` runs on the *post-core* state)
lives here too: `moverAct` re-derives the post-core Mover job, capability
liveness, regions (for the status-write authority), and the same-cycle
`sw`-store forwarding into the source word, then writes memory ports 1
(data word) and 2 (status) — port order = phase order.
-/

namespace Machines.Lnp64u.Hw

open Loom.Hw

/-! ## Small helpers -/

def dLit (d : DomainId) : Expr 2 := .lit (BitVec.ofNat 2 d.val)
def sLit (s : Slot) : Expr 4 := .lit (BitVec.ofNat 4 s.val)
def lLit (l : LineageId) : Expr 4 := .lit (BitVec.ofNat 4 l.val)
def gLit (g : GateId) : Expr 2 := .lit (BitVec.ofNat 2 g.val)
def rLit (r : RegionId) : Expr 2 := .lit (BitVec.ofNat 2 r.val)

def neqE {w : Nat} (a b : Expr w) : Expr 1 := .not (.eq a b)

/-- Opcode dispatch on the in-flight word. -/
def isMn (mn : String) : Expr 1 := .eq opcE (.lit (opcodeOf mn))

/-- Does an instruction retire this cycle? -/
def retiringE : Expr 1 := .and (.reg 1 "if_v") (.ult (.reg 8 "if_cl") (.lit 2))

def ifDomIs (d : DomainId) : Expr 1 := .eq (.reg 2 "if_dom") (dLit d)

/-- Saturating generation bump (`Kernel.bumpGen`). -/
def bumpE (g : Expr 8) : Expr 8 := .mux (.eq g (.lit 255)) g (.add g (.lit 1))

/-- `encRef` as a circuit: gen `[7:0]`, slot `[11:8]`, dom `[13:12]`. -/
def encRefE (domE : Expr 2) (slotE : Expr 4) (genE : Expr 8) : Expr 14 :=
  .or (.zext genE 14)
    (.or (.shl (.zext slotE 14) (.lit 8)) (.shl (.zext domE 14) (.lit 12)))

/-- `Handle.encode` as a circuit: slot `[3:0]`, gen `[11:4]`, class `[12]`. -/
def handleE (slotE : Expr 4) (genE : Expr 8) (clsE : Expr 1) : Expr 32 :=
  .or (.zext slotE 32)
    (.or (.shl (.zext genE 32) (.lit 4)) (.shl (.zext clsE 32) (.lit 12)))

/-- Machine-wide node index (dom ∥ slot), the `NodeId` layout. -/
def idx6 (domE : Expr 2) (slotE : Expr 4) : Expr 6 :=
  .or (.shl (.zext domE 6) (.lit 4)) (.zext slotE 6)

def nodeOf (c : DomainId) (s : Slot) : NodeId :=
  ⟨c.val * numSlots + s.val, by have := c.isLt; have := s.isLt; simp [numDomains, numSlots] at *; omega⟩

/-- Machine-wide lookups keyed by a 6-bit node index. -/
def capVAt (i6 : Expr 6) : Expr 1 :=
  muxFin (fun i : NodeId => .reg 1 (dcapV (nDom i) (nSlot i))) i6
def genAt (i6 : Expr 6) : Expr 8 :=
  muxFin (fun i : NodeId => .reg 8 (dgen (nDom i) (nSlot i))) i6
def kindWAt (i6 : Expr 6) : Expr 32 :=
  muxFin (fun i : NodeId => .reg 32 (dcapKind (nDom i) (nSlot i))) i6

/-- `MachineState.liveRef` on the pre-cycle state. -/
def liveRefE (domE : Expr 2) (slotE : Expr 4) (genE : Expr 8) : Expr 1 :=
  andAll [capVAt (idx6 domE slotE), .eq (genAt (idx6 domE slotE)) genE,
          neqE genE (.lit 0)]

/-! ## Kind-word fields (`Enc.encKind` layout) -/

def kIsMem (kw : Expr 32) : Expr 1 := .eq (field kw 0 1) (.lit 0)
def kBase (kw : Expr 32) : Expr 12 := field kw 1 12
def kLen (kw : Expr 32) : Expr 13 := field kw 13 13
def kGid (kw : Expr 32) : Expr 2 := field kw 1 2
def kR (kw : Expr 32) : Expr 1 := field kw 26 1
def kW (kw : Expr 32) : Expr 1 := field kw 27 1
def kX (kw : Expr 32) : Expr 1 := field kw 28 1

/-- `CapKind.covers` (gate kinds cover nothing; 14-bit sum, no wrap). -/
def kCovers (kw : Expr 32) (a : Expr 12) (need : Perms) : Expr 1 :=
  andAll <|
    [kIsMem kw, .not (.ult a (kBase kw)),
     .ult (.zext a 14) (.add (.zext (kBase kw) 14) (.zext (kLen kw) 14))]
    ++ (if need.r then [kR kw] else [])
    ++ (if need.w then [kW kw] else [])
    ++ (if need.x then [kX kw] else [])

/-- Pack a memory kind word from circuit fields (tag bit 0 = 0). -/
def encMemKindE (baseE : Expr 12) (lenE : Expr 13) (rE wE xE : Expr 1) :
    Expr 32 :=
  .or (.shl (.zext baseE 32) (.lit 1))
    (.or (.shl (.zext lenE 32) (.lit 13))
      (.or (.shl (.zext rE 32) (.lit 26))
        (.or (.shl (.zext wE 32) (.lit 27)) (.shl (.zext xE 32) (.lit 28)))))

/-! ## `capLive` (handle decode + generation + class agreement) -/

structure CapSel where
  /-- Entry present, generation matches, generation nonzero. -/
  live  : Expr 1
  /-- Handle class bit agrees with the entry's kind class. -/
  clsOk : Expr 1
  slot  : Expr 4
  gen   : Expr 8
  kindW : Expr 32
  linV  : Expr 1
  lin   : Expr 4

def capSel (d : DomainId) (hw : Expr 32) : CapSel :=
  let slot : Expr 4 := field hw 0 4
  let gen : Expr 8 := field hw 4 8
  let kindW := muxFin (fun s => .reg 32 (dcapKind d s)) slot
  { slot := slot, gen := gen, kindW := kindW
    live := andAll [muxFin (fun s => .reg 1 (dcapV d s)) slot,
                    .eq (muxFin (fun s => .reg 8 (dgen d s)) slot) gen,
                    neqE gen (.lit 0)]
    clsOk := .eq (field kindW 0 1) (field hw 12 1)
    linV := muxFin (fun s => .reg 1 (dcapLinV d s)) slot
    lin := muxFin (fun s => .reg 4 (dcapLin d s)) slot }

def cellVAt (d : DomainId) (linE : Expr 4) : Expr 1 :=
  muxFin (fun l => .reg 1 (dcellV d l)) linE
def cellParAt (d : DomainId) (linE : Expr 4) : Expr 14 :=
  muxFin (fun l => .reg 14 (dcellPar d l)) linE

/-! ## `freeSlot`/`freeCell` priority encoders -/

def freeSlotOk (c : DomainId) (s : Slot) : Expr 1 :=
  .and (.not (.reg 1 (dcapV c s))) (neqE (.reg 8 (dgen c s)) (.lit 255))
def freeSlotV (c : DomainId) : Expr 1 :=
  orAll ((List.finRange numSlots).map (freeSlotOk c))
def freeSlotIdx (c : DomainId) : Expr 4 :=
  (List.finRange numSlots).foldr
    (fun s acc => .mux (freeSlotOk c s) (sLit s) acc) (.lit 0)

def freeCellOk (c : DomainId) (l : LineageId) : Expr 1 :=
  .not (.reg 1 (dcellV c l))
def freeCellV (c : DomainId) : Expr 1 :=
  orAll ((List.finRange numLineage).map (freeCellOk c))
def freeCellIdx (c : DomainId) : Expr 4 :=
  (List.finRange numLineage).foldr
    (fun l acc => .mux (freeCellOk c l) (lLit l) acc) (.lit 0)

def genOfE (c : DomainId) (sE : Expr 4) : Expr 8 :=
  muxFin (fun s => .reg 8 (dgen c s)) sE

/-! ## Errno ladders -/

inductive Resp where
  | err (e : Errno)
  | fault (f : Fault)

/-- A fail condition with its response, in the spec's raise order. -/
abbrev Check := Expr 1 × Resp

def pcAdvA (d : DomainId) : Act := .write 12 (dpc d) (.add (rPc d) (.lit 1))

def respA (d : DomainId) : Resp → Act
  | .err e => .seq (pcAdvA d) (writeReg d rdE (.lit e.toWord))
  | .fault f => haltFault d f

/-- Nested-ite errno/fault ladder: first failing check wins. -/
def ladder (d : DomainId) (cs : List Check) (ok : Act) : Act :=
  cs.foldr (fun (c, r) acc => .ite c (respA d r) acc) ok

/-- All checks pass. -/
def okOf (cs : List Check) : Expr 1 := andAll (cs.map (fun c => .not c.1))

/-! ## Kernel circuit pieces -/

/-- Install an entry (and, when `linVE`, its lineage cell) at dynamic
slot/cell indices of domain `c` (`Kernel.installDerived` / the transfer
install; the cell content is `parE`). -/
def installA (c : DomainId) (nsE : Expr 4) (kindE : Expr 32) (linVE : Expr 1)
    (nlE : Expr 4) (parE : Expr 14) : Act :=
  .seq
    (seqAll ((List.finRange numSlots).map fun s =>
      .ite (.eq nsE (sLit s))
        (seqAll [.write 1 (dcapV c s) (.lit 1),
                 .write 32 (dcapKind c s) kindE,
                 .write 1 (dcapLinV c s) linVE,
                 .write 4 (dcapLin c s) nlE]) .skip))
    (seqAll ((List.finRange numLineage).map fun l =>
      .ite (.and linVE (.eq nlE (lLit l)))
        (.seq (.write 1 (dcellV c l) (.lit 1))
              (.write 14 (dcellPar c l) parE)) .skip))

/-- `Kernel.clearSlot` at a dynamic slot: clear entry, free its cell (when
the entry is derived), bump the generation saturating. -/
def clearSlotA (d : DomainId) (sE : Expr 4) (linVE : Expr 1) (linE : Expr 4) :
    Act :=
  .seq
    (seqAll ((List.finRange numSlots).map fun s =>
      .ite (.eq sE (sLit s))
        (.seq (.write 1 (dcapV d s) (.lit 0))
              (.write 8 (dgen d s) (bumpE (.reg 8 (dgen d s))))) .skip))
    (seqAll ((List.finRange numLineage).map fun l =>
      .ite (.and linVE (.eq linE (lLit l)))
        (.write 1 (dcellV d l) (.lit 0)) .skip))

/-- `Kernel.reparent`: rewrite every live cell whose parent is `oldE`. -/
def reparentA (oldE newE : Expr 14) : Act :=
  seqAll ((List.finRange numDomains).flatMap fun c =>
    (List.finRange numLineage).map fun l =>
      .ite (.and (.reg 1 (dcellV c l)) (.eq (.reg 14 (dcellPar c l)) oldE))
        (.write 14 (dcellPar c l) newE) .skip)

/-- `Kernel.orphanChildren`: free child cells, clear the childrens' entry
lineage links. -/
def orphanA (oldE : Expr 14) : Act :=
  let isChild (c : DomainId) (l : LineageId) : Expr 1 :=
    .and (.reg 1 (dcellV c l)) (.eq (.reg 14 (dcellPar c l)) oldE)
  seqAll ((List.finRange numDomains).flatMap fun c =>
    ((List.finRange numLineage).map fun l =>
      .ite (isChild c l) (.write 1 (dcellV c l) (.lit 0)) .skip)
    ++ ((List.finRange numSlots).map fun s =>
      .ite (andAll [.reg 1 (dcapV c s), .reg 1 (dcapLinV c s),
                    muxFin (fun l => isChild c l) (.reg 4 (dcapLin c s))])
        (.write 1 (dcapLinV c s) (.lit 0)) .skip))

/-- `Kernel.sweepRegions`, reachability-simplified: a valid region's backing
is live before the op (kills always sweep), so post-liveness = "not killed
by this op". -/
def sweepRegionsA (killed : Expr 2 → Expr 4 → Expr 1) : Act :=
  seqAll ((List.finRange numDomains).flatMap fun c =>
    (List.finRange numRegions).map fun r =>
      let rg : Expr 42 := .reg 42 (drgn c r)
      .ite (.and (.reg 1 (drgnV c r)) (killed (field rg 40 2) (field rg 36 4)))
        (.write 1 (drgnV c r) (.lit 0)) .skip)

def movSrcDom : Expr 2 := field (.reg 14 "mov_src") 12 2
def movSrcSlot : Expr 4 := field (.reg 14 "mov_src") 8 4
def movSrcGen : Expr 8 := field (.reg 14 "mov_src") 0 8
def movDstDom : Expr 2 := field (.reg 14 "mov_dst") 12 2
def movDstSlot : Expr 4 := field (.reg 14 "mov_dst") 8 4
def movDstGen : Expr 8 := field (.reg 14 "mov_dst") 0 8

/-- `Kernel.sweepMover`'s abort condition under this op's kill set (live
Mover jobs hold live refs on reachable states). -/
def movKilledE (killed : Expr 2 → Expr 4 → Expr 1) : Expr 1 :=
  .and (.reg 1 "mov_v")
    (.or (killed movSrcDom movSrcSlot) (killed movDstDom movDstSlot))

/-- The Mover owner's write authority over the status word, through the
*post-sweep* region registers of this op. -/
def statusAuthE (killed : Expr 2 → Expr 4 → Expr 1) : Expr 1 :=
  let sa : Expr 12 := .reg 12 "mov_status"
  orAll ((List.finRange numDomains).flatMap fun c =>
    (List.finRange numRegions).map fun r =>
      let rg : Expr 42 := .reg 42 (drgn c r)
      andAll [.eq (.reg 2 "mov_owner") (dLit c),
              .not (killed (field rg 40 2) (field rg 36 4)),
              coversE c r sa { r := false, w := true, x := false }])

/-! ## The per-op circuit record -/

structure OpCirc where
  /-- Full register behavior: ladder + ok-path writes (incl. `pc`/`rd`). -/
  act : Act
  /-- Optional core-phase memory write (single port-0 write at dispatch). -/
  memEn : Expr 1 := .lit 0
  memAddr : Expr 12 := .lit 0
  memData : Expr 32 := .lit 0

/-- Status-write `MemW` fields shared by every sweeping op. -/
def sweepMem (okE : Expr 1) (killed : Expr 2 → Expr 4 → Expr 1) : OpCirc → OpCirc :=
  fun c => { c with
    memEn := andAll [okE, movKilledE killed, statusAuthE killed]
    memAddr := .reg 12 "mov_status"
    memData := .lit Errno.staleHandle.toWord }

/-! ## cap_dup / mem_grant (narrow + install) -/

/-- The packed descriptor's fields (`Isa/System.lean`). -/
def descTgt (dw : Expr 32) : Expr 2 := field dw 0 2
def descR (dw : Expr 32) : Expr 1 := field dw 2 1
def descW (dw : Expr 32) : Expr 1 := field dw 3 1
def descX (dw : Expr 32) : Expr 1 := field dw 4 1
def descOffE (dw : Expr 32) : Expr 12 := field dw 5 12
def descLenE (dw : Expr 32) : Expr 13 := field dw 17 13

/-- `narrow`'s fail conditions against parent kind `kw` (assumed mem where
they fire; `pre` guards the whole list — `cap_dup` skips narrowing for gate
kinds). -/
def narrowChecks (pre : Expr 1) (kw dw : Expr 32) : List Check :=
  [ (.and pre (.ult (.zext (kLen kw) 14)
      (.add (.zext (descOffE dw) 14) (.zext (descLenE dw) 14))), .err .outOfRange),
    (.and pre (.not (.ult (.add (.zext (kBase kw) 13) (.zext (descOffE dw) 13))
      (.lit 4096))), .err .outOfRange),
    (.and pre (orAll [.and (descR dw) (.not (kR kw)),
                      .and (descW dw) (.not (kW kw)),
                      .and (descX dw) (.not (kX kw))]), .err .permDenied),
    (.and pre (.and (descW dw) (descX dw)), .err .permDenied) ]

/-- The narrowed kind word. -/
def narrowKindE (kw dw : Expr 32) : Expr 32 :=
  encMemKindE (.add (kBase kw) (descOffE dw)) (descLenE dw)
    (descR dw) (descW dw) (descX dw)

def dupSel (d : DomainId) : CapSel := capSel d (readReg d rs1E)

def dupChecks (d : DomainId) : List Check :=
  let cs := dupSel d
  let dw := readReg d rs2E
  [ (.not cs.live, .err .staleHandle), (.not cs.clsOk, .err .badCap) ]
  ++ narrowChecks (kIsMem cs.kindW) cs.kindW dw
  ++ [ (.not (freeSlotV d), .err .slotOccupied),
       (.not (freeCellV d), .err .noLineage) ]

def dupCirc (d : DomainId) : OpCirc :=
  let cs := dupSel d
  let dw := readReg d rs2E
  let ns := freeSlotIdx d
  let nl := freeCellIdx d
  let newKind := .mux (kIsMem cs.kindW) (narrowKindE cs.kindW dw) cs.kindW
  let par := encRefE (dLit d) cs.slot cs.gen
  { act := ladder d (dupChecks d) <| seqAll
      [ installA d ns newKind (.lit 1) nl par,
        writeReg d rdE (handleE ns (genOfE d ns) (field cs.kindW 0 1)),
        pcAdvA d ] }

def grantSel (d : DomainId) : CapSel := capSel d (readReg d rs1E)

def grantChecks (d : DomainId) : List Check :=
  let cs := grantSel d
  let dw := readReg d rs2E
  [ (.not cs.live, .err .staleHandle),
    (.not (.and cs.clsOk (kIsMem cs.kindW)), .err .badCap) ]
  ++ narrowChecks (.lit 1) cs.kindW dw
  ++ [ (.not (muxFin (fun c => freeSlotV c) (descTgt dw)), .err .slotOccupied),
       (.not (muxFin (fun c => freeCellV c) (descTgt dw)), .err .noLineage) ]

def grantCirc (d : DomainId) : OpCirc :=
  let cs := grantSel d
  let dw := readReg d rs2E
  let tE := descTgt dw
  let newKind := narrowKindE cs.kindW dw
  let par := encRefE (dLit d) cs.slot cs.gen
  { act := ladder d (grantChecks d) <| seqAll
      [ seqAll ((List.finRange numDomains).map fun c =>
          .ite (.eq tE (dLit c))
            (installA c (freeSlotIdx c) newKind (.lit 1) (freeCellIdx c) par)
            .skip),
        writeReg d rdE (muxFin (fun c =>
          handleE (freeSlotIdx c) (genOfE c (freeSlotIdx c)) (.lit 0)) tE),
        pcAdvA d ] }

/-! ## cap_drop -/

def dropSel (d : DomainId) : CapSel := capSel d (readReg d rs1E)

def dropChecks (d : DomainId) : List Check :=
  let cs := dropSel d
  [ (.not cs.live, .err .staleHandle), (.not cs.clsOk, .err .badCap) ]

def dropOkE (d : DomainId) : Expr 1 := okOf (dropChecks d)

def dropKilled (d : DomainId) (dm : Expr 2) (sl : Expr 4) : Expr 1 :=
  .and (.eq dm (dLit d)) (.eq sl (dropSel d).slot)

def dropCirc (d : DomainId) : OpCirc :=
  let cs := dropSel d
  let oldE := encRefE (dLit d) cs.slot cs.gen
  let pEx := .and cs.linV (cellVAt d cs.lin)
  let pEnc := cellParAt d cs.lin
  sweepMem (dropOkE d) (dropKilled d)
  { act := ladder d (dropChecks d) <| seqAll
      [ .ite pEx (reparentA oldE pEnc) (orphanA oldE),
        clearSlotA d cs.slot cs.linV cs.lin,
        sweepRegionsA (dropKilled d),
        writeReg d rdE (.lit 0),
        pcAdvA d ] }

/-! ## cap_revoke (mark engine + destroyMarked) -/

/-- Marks vector lookup at a dynamic node. -/
def marksAt (dm : Expr 2) (sl : Expr 4) : Expr 1 :=
  muxFin (fun i : NodeId => .reg 1 (rvR i)) (idx6 dm sl)

def revSel (d : DomainId) : CapSel := capSel d (readReg d rs1E)

def revChecks (d : DomainId) : List Check :=
  let cs := revSel d
  [ (.not cs.live, .err .staleHandle),
    (.not (.and cs.clsOk (kIsMem cs.kindW)), .err .badCap) ]

def revOkE (d : DomainId) : Expr 1 := okOf (revChecks d)

def revKilled (dm : Expr 2) (sl : Expr 4) : Expr 1 := marksAt dm sl

def revCirc (d : DomainId) : OpCirc :=
  sweepMem (revOkE d) revKilled
  { act := ladder d (revChecks d) <| seqAll <|
      -- destroyMarked: entries + generations
      ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numSlots).map fun s =>
          .ite (.and (.reg 1 (rvR (nodeOf c s))) (.reg 1 (dcapV c s)))
            (.seq (.write 1 (dcapV c s) (.lit 0))
                  (.write 8 (dgen c s) (bumpE (.reg 8 (dgen c s))))) .skip)
      -- destroyMarked: dead cells
      ++ ((List.finRange numDomains).flatMap fun c =>
        (List.finRange numLineage).map fun l =>
          .ite (orAll ((List.finRange numSlots).map fun s =>
              andAll [.reg 1 (rvR (nodeOf c s)), .reg 1 (dcapV c s),
                      .reg 1 (dcapLinV c s),
                      .eq (.reg 4 (dcapLin c s)) (lLit l)]))
            (.write 1 (dcellV c l) (.lit 0)) .skip)
      ++ [ sweepRegionsA revKilled,
           writeReg d rdE (.lit 0),
           pcAdvA d ] }

/-- `cap_revoke`'s WCET (24): the number of cycles it holds the core, and
therefore the mark engine's doubling-round budget. -/
def revokeCost : Nat :=
  ((isa.toList.find? (·.mnemonic = "cap_revoke")).map (·.cost.cost)).getD 24

/-- Initialization of the pointer-doubling mark engine, run on the *first
countdown cycle* of an in-flight `cap_revoke` (`if_cl = revokeCost`; the
issuing domain's registers and every cap table are stable while the
instruction is in flight, and keying off the cheap `if_*` registers keeps
the scheduler conditions out of 192 hidden registers' next-value
expressions). Per node: the parent edge (exists / live-gen / hits root)
and the parent's node index. -/
def rvInit : Act :=
  let hw := muxFin (fun d => readReg d rs1E) (.reg 2 "if_dom")
  let rootEnc := encRefE (.reg 2 "if_dom") (field hw 0 4) (field hw 4 8)
  seqAll ((List.finRange (numDomains * numSlots)).map fun i =>
    let c := nDom i
    let s := nSlot i
    let linE : Expr 4 := .reg 4 (dcapLin c s)
    let pEx := andAll [.reg 1 (dcapV c s), .reg 1 (dcapLinV c s), cellVAt c linE]
    let pEnc := cellParAt c linE
    let pIdx : Expr 6 := field pEnc 8 6
    seqAll
      [ .write 6 (rvJ i) pIdx,
        .write 1 (rvV i) (.and pEx (.eq (genAt pIdx) (field pEnc 0 8))),
        .write 1 (rvR i) (.and pEx (.eq pEnc rootEnc)) ])

/-- One pointer-doubling round (run each countdown cycle of an in-flight
`cap_revoke`): `R += V ∧ R[J]`, `V &= V[J]`, `J := J[J]`. After `k` rounds
`R i` covers parent chains of length `≤ 2^k`; ≥ 7 rounds = the `marks`
closure, and the 24-cycle WCET provides 23. -/
def rvStep : Act :=
  seqAll ((List.finRange (numDomains * numSlots)).map fun i =>
    let j : Expr 6 := .reg 6 (rvJ i)
    seqAll
      [ .write 1 (rvR i) (.or (.reg 1 (rvR i))
          (.and (.reg 1 (rvV i)) (muxFin (fun k : NodeId => .reg 1 (rvR k)) j))),
        .write 1 (rvV i) (.and (.reg 1 (rvV i))
          (muxFin (fun k : NodeId => .reg 1 (rvV k)) j)),
        .write 6 (rvJ i) (muxFin (fun k : NodeId => .reg 6 (rvJ k)) j) ])

/-! ## map / unmap -/

def mapSel (d : DomainId) : CapSel := capSel d (readReg d rs1E)

def mapChecks (d : DomainId) : List Check :=
  let cs := mapSel d
  [ (.not cs.live, .err .staleHandle),
    (.not (.and cs.clsOk (kIsMem cs.kindW)), .err .badCap) ]

def mapOkE (d : DomainId) : Expr 1 := okOf (mapChecks d)

/-- The packed region value `map` writes (`Enc.encRegion` layout). -/
def mapValE (d : DomainId) : Expr 42 :=
  let cs := mapSel d
  .or (.zext (field cs.kindW 26 3) 42)
    (.or (.shl (.zext (kLen cs.kindW) 42) (.lit 3))
      (.or (.shl (.zext (kBase cs.kindW) 42) (.lit 16))
        (.shl (.zext (encRefE (dLit d) cs.slot cs.gen) 42) (.lit 28))))

def riE : Expr 2 := field immE 0 2

def mapCirc (d : DomainId) : OpCirc :=
  { act := ladder d (mapChecks d) <| seqAll <|
      ((List.finRange numRegions).map fun r =>
        .ite (.eq riE (rLit r))
          (.seq (.write 1 (drgnV d r) (.lit 1))
                (.write 42 (drgn d r) (mapValE d))) .skip)
      ++ [writeReg d rdE (.lit 0), pcAdvA d] }

def unmapCirc (d : DomainId) : OpCirc :=
  { act := seqAll <|
      ((List.finRange numRegions).map fun r =>
        .ite (.eq riE (rLit r)) (.write 1 (drgnV d r) (.lit 0)) .skip)
      ++ [writeReg d rdE (.lit 0), pcAdvA d] }

/-! ## Capability transfer (`Kernel.transferCap`), shared by the gate ops -/

/-- Can the transfer of `acs` from `d` to the (dynamic) domain `toE` *not*
be placed (`transferCap = none` ⇒ `-ESLOTOCCUPIED`)? -/
def transferBlocked (d : DomainId) (toE : Expr 2) (acs : CapSel) : Expr 1 :=
  .or (.not (muxFin (fun c => freeSlotV c) toE))
      (.and acs.linV (.or (.not (cellVAt d acs.lin))
                          (.not (muxFin (fun c => freeCellV c) toE))))

/-- The moved capability's recipient-relative handle. -/
def transferHandleAt (toE : Expr 2) (acs : CapSel) : Expr 32 :=
  muxFin (fun c =>
    handleE (freeSlotIdx c) (genOfE c (freeSlotIdx c)) (field acs.kindW 0 1)) toE

/-- The transfer composite: install at recipient (cell moves, reparent
applied to the moved cell's own content), machine-wide reparent to the new
reference, clear the source slot, sweep regions. (`sweepMover`'s register
half is owned by the Mover rule; its status write is the op's `MemW`.) -/
def transferA (d : DomainId) (toE : Expr 2) (acs : CapSel) : Act :=
  let oldE := encRefE (dLit d) acs.slot acs.gen
  let srcPar := cellParAt d acs.lin
  let newAt := muxFin (fun c =>
    encRefE (dLit c) (freeSlotIdx c) (genOfE c (freeSlotIdx c))) toE
  seqAll
    [ seqAll ((List.finRange numDomains).map fun c =>
        .ite (.eq toE (dLit c))
          (let ns := freeSlotIdx c
           let newE := encRefE (dLit c) ns (genOfE c ns)
           installA c ns acs.kindW acs.linV (freeCellIdx c)
             (.mux (.eq srcPar oldE) newE srcPar)) .skip),
      reparentA oldE newAt,
      clearSlotA d acs.slot acs.linV acs.lin,
      sweepRegionsA (fun dm sl => .and (.eq dm (dLit d)) (.eq sl acs.slot)) ]

/-! ## gate_call -/

def callSel (d : DomainId) : CapSel := capSel d (readReg d rs1E)
def callGid (d : DomainId) : Expr 2 := kGid (callSel d).kindW
def callCal (d : DomainId) : Expr 2 :=
  muxFin (fun g => .reg 2 (gcallee g)) (callGid d)
def argW (d : DomainId) : Expr 32 := readReg d rs2E
def argNZ (d : DomainId) : Expr 1 := neqE (argW d) (.lit 0)
def argSel (d : DomainId) : CapSel := capSel d (argW d)

/-- The activation chain depth this call would create. -/
def callDepth (d : DomainId) : Expr 3 :=
  let g' : Expr 2 := .reg 2 (dsrv d)
  .mux (.and (.reg 1 (dsrvV d)) (muxFin (fun g => .reg 1 (gactV g)) g'))
       (.add (muxFin (fun g => .reg 3 (gdepth g)) g') (.lit 1)) (.lit 1)

def callChecks (d : DomainId) : List Check :=
  let cs := callSel d
  let gid := callGid d
  let cal := callCal d
  let acs := argSel d
  [ (.not cs.live, .err .staleHandle),
    (.not (.and cs.clsOk (.not (kIsMem cs.kindW))), .err .badCap),
    (muxFin (fun g => .reg 1 (gactV g)) gid, .err .gateBusy),
    (.eq cal (dLit d), .err .gateBusy),
    (neqE (muxFin (fun c => .reg 2 (drun c)) cal) (.lit 0), .err .gateBusy),
    (muxFin (fun c => .reg 1 (dsrvV c)) cal, .err .gateBusy),
    (.ult (.lit (BitVec.ofNat 3 maxChainDepth)) (callDepth d), .err .gateBusy),
    (.and (argNZ d) (.not acs.live), .err .staleHandle),
    (.and (argNZ d) (.not acs.clsOk), .err .badCap),
    (.and (argNZ d) (transferBlocked d cal acs), .err .slotOccupied) ]

def callOkE (d : DomainId) : Expr 1 := okOf (callChecks d)

def callKilled (d : DomainId) (dm : Expr 2) (sl : Expr 4) : Expr 1 :=
  andAll [argNZ d, .eq dm (dLit d), .eq sl (argSel d).slot]

def callCirc (d : DomainId) : OpCirc :=
  let gid := callGid d
  let cal := callCal d
  let acs := argSel d
  let argH := .mux (argNZ d) (transferHandleAt cal acs) (.lit 0)
  sweepMem (callOkE d) (callKilled d)
  { act := ladder d (callChecks d) <| seqAll
      [ .ite (argNZ d) (transferA d cal acs) .skip,
        -- activation record (savedRegs = the callee's pre-cycle file)
        seqAll ((List.finRange numGates).map fun g =>
          .ite (.eq gid (gLit g)) (seqAll <|
            [ .write 1 (gactV g) (.lit 1),
              .write 2 (gcaller g) (dLit d),
              .write 3 (gcallerRd g) rdE ]
            ++ ((List.finRange numRegs).map fun r =>
                .write 32 (gsreg g r) (muxFin (fun c => .reg 32 (dreg c r)) cal))
            ++ [ .write 12 (gspc g) (muxFin (fun c => .reg 12 (dpc c)) cal),
                 .write 1 (gssrvV g) (muxFin (fun c => .reg 1 (dsrvV c)) cal),
                 .write 2 (gssrv g) (muxFin (fun c => .reg 2 (dsrv c)) cal),
                 .write 3 (gdepth g) (callDepth d),
                 .write 32 (gdon g) (.reg 32 (dmaxdon d)) ]) .skip),
        -- callee scrub + entry
        seqAll ((List.finRange numDomains).map fun c =>
          .ite (.eq cal (dLit c)) (seqAll <|
            ((List.finRange numRegs).map fun r =>
              .write 32 (dreg c r) (if r.val = 1 then argH else .lit 0))
            ++ [ .write 12 (dpc c) (muxFin (fun g => .reg 12 (gentry g)) gid),
                 .write 1 (dsrvV c) (.lit 1),
                 .write 2 (dsrv c) gid ]) .skip),
        -- caller blocks
        .write 2 (drun d) (.lit 2),
        .write 2 (drunG d) gid,
        pcAdvA d ] }

/-! ## gate_return -/

def retGid (d : DomainId) : Expr 2 := .reg 2 (dsrv d)
def retCl (d : DomainId) : Expr 2 :=
  muxFin (fun g => .reg 2 (gcaller g)) (retGid d)
def retW (d : DomainId) : Expr 32 := readReg d rs1E
def retNZ (d : DomainId) : Expr 1 := neqE (retW d) (.lit 0)
def retSel (d : DomainId) : CapSel := capSel d (retW d)

def retChecks (d : DomainId) : List Check :=
  [ (.not (.reg 1 (dsrvV d)), .fault .protocol),
    (.not (muxFin (fun g => .reg 1 (gactV g)) (retGid d)), .fault .protocol),
    (.and (retNZ d) (.not (retSel d).live), .err .staleHandle),
    (.and (retNZ d) (.not (retSel d).clsOk), .err .badCap),
    (.and (retNZ d) (transferBlocked d (retCl d) (retSel d)),
      .err .slotOccupied) ]

def retOkE (d : DomainId) : Expr 1 := okOf (retChecks d)

def retKilled (d : DomainId) (dm : Expr 2) (sl : Expr 4) : Expr 1 :=
  andAll [retNZ d, .eq dm (dLit d), .eq sl (retSel d).slot]

def retCirc (d : DomainId) : OpCirc :=
  let gid := retGid d
  let cl := retCl d
  let rcs := retSel d
  let reply := .mux (retNZ d) (transferHandleAt cl rcs) (.lit 0)
  sweepMem (retOkE d) (retKilled d)
  { act := ladder d (retChecks d) <| seqAll
      [ .ite (retNZ d) (transferA d cl rcs) .skip,
        seqAll ((List.finRange numGates).map fun g =>
          .ite (.eq gid (gLit g)) (.write 1 (gactV g) (.lit 0)) .skip),
        -- restore the serving domain's saved context
        seqAll ((List.finRange numRegs).map fun r =>
          .write 32 (dreg d r) (muxFin (fun g => .reg 32 (gsreg g r)) gid)),
        .write 12 (dpc d) (muxFin (fun g => .reg 12 (gspc g)) gid),
        .write 1 (dsrvV d) (muxFin (fun g => .reg 1 (gssrvV g)) gid),
        .write 2 (dsrv d) (muxFin (fun g => .reg 2 (gssrv g)) gid),
        -- caller resumes with the reply
        seqAll ((List.finRange numDomains).map fun c =>
          .ite (.eq cl (dLit c)) (.write 2 (drun c) (.lit 0)) .skip),
        (let rdi := muxFin (fun g => .reg 3 (gcallerRd g)) gid
         seqAll ((List.finRange numDomains).map fun c =>
          .ite (.eq cl (dLit c)) (writeReg c rdi reply) .skip)) ] }

/-! ## move (Mover job programming) -/

structure MoveJobE where
  ok : Expr 1
  srcEnc : Expr 14
  dstEnc : Expr 14
  srcCur : Expr 12
  dstCur : Expr 12
  sa : Expr 12
  rem : Expr 13

def moveBase (d : DomainId) : Expr 12 := field (readReg d rs1E) 0 12
def moveW (d : DomainId) (i : Nat) : Expr 32 :=
  .memRead 32 "mem" (.add (moveBase d) (.lit (BitVec.ofNat 12 i)))
def moveSrcSel (d : DomainId) : CapSel := capSel d (moveW d 0)
def moveDstSel (d : DomainId) : CapSel := capSel d (moveW d 1)

def moveChecks (d : DomainId) : List Check :=
  let scs := moveSrcSel d
  let dcs := moveDstSel d
  let n32 := moveW d 2
  let rdChk (i : Nat) : Check :=
    (.not (domCoversE d (.add (moveBase d) (.lit (BitVec.ofNat 12 i)))
      { r := true, w := false, x := false }), .fault .memoryAuthority)
  [ (.reg 1 "mov_v", .err .moverBusy),
    rdChk 0, rdChk 1, rdChk 2, rdChk 3,
    (.not scs.live, .err .staleHandle), (.not scs.clsOk, .err .badCap),
    (.not dcs.live, .err .staleHandle), (.not dcs.clsOk, .err .badCap),
    (.not (.and (kIsMem scs.kindW) (kIsMem dcs.kindW)), .err .badCap),
    (.not (kR scs.kindW), .err .permDenied),
    (.not (kW dcs.kindW), .err .permDenied),
    (.or (.ult (.zext (kLen scs.kindW) 32) n32)
         (.ult (.zext (kLen dcs.kindW) 32) n32), .err .outOfRange),
    (.not (domCoversE d (field (moveW d 3) 0 12)
      { r := false, w := true, x := false }), .fault .memoryAuthority) ]

def moveJob (d : DomainId) : MoveJobE :=
  let scs := moveSrcSel d
  let dcs := moveDstSel d
  { ok := okOf (moveChecks d)
    srcEnc := encRefE (dLit d) scs.slot scs.gen
    dstEnc := encRefE (dLit d) dcs.slot dcs.gen
    srcCur := kBase scs.kindW
    dstCur := kBase dcs.kindW
    sa := field (moveW d 3) 0 12
    rem := field (moveW d 2) 0 13 }

def moveCirc (d : DomainId) : OpCirc :=
  { act := ladder d (moveChecks d)
      (.seq (writeReg d rdE (.lit 0)) (pcAdvA d)) }

/-! ## yield / halt -/

def yieldCirc (d : DomainId) : OpCirc :=
  { act := seqAll [.write 32 (dbudget d) (.lit 0),
                   writeReg d rdE (.lit 0), pcAdvA d] }

def haltCirc (d : DomainId) : OpCirc :=
  { act := .seq (pcAdvA d) (haltAct d 0) }

/-! ## Base-op circuits (moved from the old `retireFor`; `sw`'s store is now
the dispatch-level port-0 write) -/

def baseCircs (d : DomainId) : List (String × OpCirc) :=
  let pc := rPc d
  let a := readReg d rs1E
  let b := readReg d rs2E
  let alu (v : Expr 32) : OpCirc := { act := .seq (writeReg d rdE v) (pcAdvA d) }
  let eaddr : Expr 12 := field (.add a immX) 0 12
  let btgt : Expr 12 := .add pc (field immX 0 12)
  [ ("add", alu (.add a b)), ("sub", alu (.sub a b)),
    ("and", alu (.and a b)), ("or", alu (.or a b)), ("xor", alu (.xor a b)),
    ("shl", alu (.shl a (.and b (.lit 31)))),
    ("shr", alu (.shr a (.and b (.lit 31)))),
    ("addi", alu (.add a immX)),
    ("lui", alu (.shl (.zext immE 32) (.lit 15))),
    ("lw", { act := .ite (domCoversE d eaddr ⟨true, false, false⟩)
                      (.seq (writeReg d rdE (.memRead 32 "mem" eaddr)) (pcAdvA d))
                      (haltFault d .memoryAuthority) }),
    ("sw", { act := .ite (domCoversE d eaddr ⟨false, true, false⟩)
               (pcAdvA d) (haltFault d .memoryAuthority)
             memEn := domCoversE d eaddr ⟨false, true, false⟩
             memAddr := eaddr, memData := b }),
    ("beq", { act := .ite (.eq a b) (.write 12 (dpc d) btgt) (pcAdvA d) }),
    ("blt", { act := .ite (.slt a b) (.write 12 (dpc d) btgt) (pcAdvA d) }),
    ("jalr", { act := .seq (writeReg d rdE (.zext (.add pc (.lit 1)) 32))
                 (.write 12 (dpc d) eaddr) }) ]

/-! ## The full dispatch -/

/-- All 25 opcode circuits of domain `d`. -/
def opCircs (d : DomainId) : List (String × OpCirc) :=
  baseCircs d ++
  [ ("cap_dup", dupCirc d), ("cap_drop", dropCirc d),
    ("cap_revoke", revCirc d), ("mem_grant", grantCirc d),
    ("map", mapCirc d), ("unmap", unmapCirc d),
    ("gate_call", callCirc d), ("gate_return", retCirc d),
    ("move", moveCirc d), ("yield", yieldCirc d), ("halt", haltCirc d) ]

/-- Retirement register behavior for domain `d` (mirrors `Step.retire`;
the decode-failure fallback is unreachable for issued words). -/
def retireFor (d : DomainId) : Act :=
  (opCircs d).foldr (fun (mn, c) acc => .ite (isMn mn) c.act acc)
    (haltFault d .illegalInstruction)

/-- Retirement memory-write triple for domain `d` (the ops' port-0 writes,
muxed; opcodes are mutually exclusive). -/
def retireMemFor (d : DomainId) : Expr 1 × Expr 12 × Expr 32 :=
  (opCircs d).foldr
    (fun (mn, c) (en, ad, da) =>
      let g := .and (isMn mn) c.memEn
      (.or g en, .mux g c.memAddr ad, .mux g c.memData da))
    (.lit 0, .lit 0, .lit 0)

/-! ## The Mover rule's post-core composites -/

/-- Was the reference `(dm, sl)` killed by this cycle's retirement (slot
cleared / generation bumped)? The union of the four killing ops' kill sets,
gated by each op's ok condition. -/
def killedByCoreE (dm : Expr 2) (sl : Expr 4) : Expr 1 :=
  .and retiringE <| orAll ((List.finRange numDomains).map fun d =>
    .and (ifDomIs d) (orAll
      [ .and (isMn "cap_drop") (.and (dropOkE d) (dropKilled d dm sl)),
        .and (isMn "cap_revoke") (.and (revOkE d) (revKilled dm sl)),
        .and (isMn "gate_call") (.and (callOkE d) (callKilled d dm sl)),
        .and (isMn "gate_return") (.and (retOkE d) (retKilled d dm sl)) ]))

/-- Did domain `d` retire a successful `move` this cycle? -/
def newJobSet (d : DomainId) : Expr 1 :=
  andAll [retiringE, ifDomIs d, isMn "move", (moveJob d).ok]

/-- Post-core Mover field: the retiring `move`'s value, else the register. -/
def postJ {w : Nat} (f : DomainId → Expr w) (cur : Expr w) : Expr w :=
  (List.finRange numDomains).foldr
    (fun d acc => .mux (newJobSet d) (f d) acc) cur

/-- Post-core region validity/value of `(c, r)` — the retiring op's
`map`/`unmap`/sweep applied on top of the registers. -/
def rgnVPostE (c : DomainId) (r : RegionId) : Expr 1 :=
  let mapSet := andAll [retiringE, ifDomIs c, isMn "map", mapOkE c,
                        .eq riE (rLit r)]
  let unmapSet := andAll [retiringE, ifDomIs c, isMn "unmap", .eq riE (rLit r)]
  let rg : Expr 42 := .reg 42 (drgn c r)
  .mux mapSet (.lit 1) <| .mux unmapSet (.lit 0) <|
    .and (.reg 1 (drgnV c r))
         (.not (killedByCoreE (field rg 40 2) (field rg 36 4)))

def rgnValPostE (c : DomainId) (r : RegionId) : Expr 42 :=
  let mapSet := andAll [retiringE, ifDomIs c, isMn "map", mapOkE c,
                        .eq riE (rLit r)]
  .mux mapSet (mapValE c) (.reg 42 (drgn c r))

/-- `Region.covers` on a packed region value. -/
def rgnCoversVal (rv : Expr 42) (a : Expr 12) (need : Perms) : Expr 1 :=
  let base : Expr 12 := field rv 16 12
  let len : Expr 13 := field rv 3 13
  andAll <|
    [.not (.ult a base),
     .ult (.zext a 14) (.add (.zext base 14) (.zext len 14))]
    ++ (if need.r then [field rv 0 1] else [])
    ++ (if need.w then [field rv 1 1] else [])
    ++ (if need.x then [field rv 2 1] else [])

/-- Rule 3: the Mover phase (`Step.moverPhase`) on the post-core state.
Owns all `mov_*` registers (the core's `move`-install and sweep-clears are
folded in here); memory port 1 carries the data word, port 2 the status
word — ascending port order = spec write order. -/
def moverAct : Act :=
  let cleared := .and (.reg 1 "mov_v")
    (.or (killedByCoreE movSrcDom movSrcSlot)
         (killedByCoreE movDstDom movDstSlot))
  let newAny := orAll ((List.finRange numDomains).map newJobSet)
  let jobV := .or newAny (.and (.reg 1 "mov_v") (.not cleared))
  let srcE := postJ (fun d => (moveJob d).srcEnc) (.reg 14 "mov_src")
  let dstE := postJ (fun d => (moveJob d).dstEnc) (.reg 14 "mov_dst")
  let ownerE := postJ (fun d => dLit d) (.reg 2 "mov_owner")
  let srcCur := postJ (fun d => (moveJob d).srcCur) (.reg 12 "mov_srccur")
  let dstCur := postJ (fun d => (moveJob d).dstCur) (.reg 12 "mov_dstcur")
  let rem := postJ (fun d => (moveJob d).rem) (.reg 13 "mov_rem")
  let sa := postJ (fun d => (moveJob d).sa) (.reg 12 "mov_status")
  -- per-word re-check on the post-core capability tables (live-pre ∧ not
  -- killed this cycle; entries never mutate in place)
  let liveP (e : Expr 14) : Expr 1 :=
    .and (liveRefE (field e 12 2) (field e 8 4) (field e 0 8))
         (.not (killedByCoreE (field e 12 2) (field e 8 4)))
  let checkOk := andAll
    [ liveP srcE, kCovers (kindWAt (field srcE 8 6)) srcCur ⟨true, false, false⟩,
      liveP dstE, kCovers (kindWAt (field dstE 8 6)) dstCur ⟨false, true, false⟩ ]
  -- source word with same-cycle core-store forwarding
  let srcWord := (List.finRange numDomains).foldr
    (fun d acc =>
      let eaddr : Expr 12 := field (.add (readReg d rs1E) immX) 0 12
      let hit := andAll [retiringE, ifDomIs d, isMn "sw",
                         domCoversE d eaddr ⟨false, true, false⟩,
                         .eq eaddr srcCur]
      .mux hit (readReg d rs2E) acc)
    (.memRead 32 "mem" srcCur)
  -- status-write authority through the post-core regions of the owner
  let sAuth := orAll ((List.finRange numDomains).flatMap fun c =>
    (List.finRange numRegions).map fun r =>
      andAll [.eq ownerE (dLit c), rgnVPostE c r,
              rgnCoversVal (rgnValPostE c r) sa ⟨false, true, false⟩])
  let moveWord := .and (neqE rem (.lit 0)) checkOk
  let statusEn := .and sAuth
    (.or (.eq rem (.lit 0)) (.or (.not checkOk) (.eq rem (.lit 1))))
  let statusData : Expr 32 :=
    .mux (.and (neqE rem (.lit 0)) (.not checkOk))
      (.lit Errno.staleHandle.toWord) (.lit 1)
  let contE := .and moveWord (neqE rem (.lit 1))
  .ite jobV
    (seqAll
      [ .ite moveWord (.memWrite 12 32 "mem" 1 dstCur srcWord) .skip,
        .ite statusEn (.memWrite 12 32 "mem" 2 sa statusData) .skip,
        .write 1 "mov_v" contE,
        .write 14 "mov_src" srcE,
        .write 14 "mov_dst" dstE,
        .write 2 "mov_owner" ownerE,
        .write 12 "mov_status" sa,
        .write 12 "mov_srccur" (.add srcCur (.lit 1)),
        .write 12 "mov_dstcur" (.add dstCur (.lit 1)),
        .write 13 "mov_rem" (.sub rem (.lit 1)) ])
    (.write 1 "mov_v" (.lit 0))

end Machines.Lnp64u.Hw
