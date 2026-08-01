-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Netlist.Netlist
import Loom.Emit.MicroVerilog.Ast
import Loom.Hw.MemInitOk

/-!
# Memory banks inside the equivalence check (D31)

Until D31 the checker treated every memory hard block as a *cut point*: the
array's contents, its write ports' wiring and its configuration image were
"carried by cell identity", i.e. trusted. D30 is what that cost — yosys
mapped a 512×3 bank to distributed LUT RAM, the bitstream path silently
dropped its non-zero reset image, and no stage of the flow said a word; the
defect surfaced on silicon.

This module resolves each memory primitive `synth_xilinx` emits into a
width/depth-explicit interface — write address / enable / clock / data pins,
read ports, and the configuration image the primitive's `INIT*` parameters
encode — and reassembles the primitives of one µVerilog `MemDef` into a
**bank**: a `nRepl × nDepth × nLane` grid of cells covering the declared
address × data space. Everything here is structural and pure; the *cone*
comparisons that check a bank's pins against the IR's `WritePort`
expressions are built on top of it in `Tools/EqCheck.lean`, out of the same
`coneMiter` the rest of the checker uses.

Untrusted, like the rest of `Loom/Netlist/*`: this is the "if the encoding
is faithful" side of the claim (`EQCHECK_SPEC.md`). What it must never do
is *silently* accept something — every shape it cannot resolve is an error
naming the bank and the cell.
-/

namespace Loom.Netlist

open Loom.Emit.MicroVerilog

/-! ## yosys parameter strings -/

/-- A yosys bit-string parameter read as an unsigned binary number
(most-significant bit first). `none` if it is not a `0`/`1` string. -/
def paramNat (s : String) : Option Nat :=
  s.foldl (fun acc c =>
    match acc, c with
    | some n, '0' => some (2 * n)
    | some n, '1' => some (2 * n + 1)
    | _, _ => none) (some 0)

/-- Bit `i` (LSB = 0) of a yosys bit-string parameter. `x`/`z` — an
uninitialized location — reads as `0`, which is what the fabric delivers;
a missing parameter is all-zero. -/
def paramBit (s : String) (i : Nat) : Bool :=
  let cs := s.toList
  let n := cs.length
  if i ≥ n then false else (cs[n - 1 - i]!) == '1'

/-- Number of `1`s in a parameter string. -/
def paramOnes (s : String) : Nat :=
  s.foldl (fun n c => if c == '1' then n + 1 else n) 0

/-! ## Primitive families -/

/-! Which primitive family holds a bank, and hence whether the
configuration path delivers its reset image — **defined in
`Loom/Hw/MemInitOk.lean`** and re-exported here.

The distinction is the whole of D30: a `RAMB*` image is part of the
bitstream and arrives; a distributed-RAM (`RAM*`) image is *not* delivered
by the openXC7 path — the bank powers up all-zero, with no diagnostic at
any stage (`LOOM_GAPS.md` D30, `Machines/Epoch/EPOCH_SPEC.md` E13).

It lives at the design layer because D37 turned that distinction into a
*design-level* refusal: `Loom.Hw.Design.memInitOkB` predicts the family
from a `MemDecl`'s declared shape and asks the very same question of it —
`Loom.Hw.imageDelivered` — that `checkImage` below asks of the family it
observes in the netlist. One type, one rule, two sources of the family. -/

export Loom.Hw (MemFamily imageDelivered)

def memFamily (ty : String) : Option MemFamily :=
  if ty == "RAMB18E1" || ty == "RAMB36E1" || ty == "RAMB18" || ty == "RAMB36" then
    some .bram
  else if (memCellPorts ty).isSome then some .lutram
  else none

/-! ## One primitive, resolved -/

/-- A memory primitive with its geometry and pins made explicit.

`image a j` is content bit `j` of address `a` *of this cell*, as the
primitive's `INIT*` parameters encode it. `wrData`/`rdPorts` are indexed in
the same cell-word order, so the bank assembly below can lay a µVerilog
word across cells without knowing anything about the primitive. -/
structure CellIface where
  name     : String
  ty       : String
  family   : MemFamily
  /-- addresses this cell holds -/
  depth    : Nat
  /-- content bits per address -/
  width    : Nat
  wrAddr   : Array SigBit
  wrEn     : Array SigBit
  wrClk    : Array SigBit
  wrData   : Array SigBit
  /-- `(address pins, data pins)` per read port, data in cell-word order. -/
  rdPorts  : Array (Array SigBit × Array SigBit)
  /-- block RAM reads are synchronous (one cycle, D19); LUT RAM is async. -/
  syncRead : Bool
  /-- a *second* pipeline register on the data output (`DOx_REG`): two
  cycles of latency, which is not the D19 shape. -/
  regOut   : Bool := false
  /-- the write mode the primitive is configured in (`READ_FIRST` is the
  µVerilog semantics: a read sees the pre-cycle contents). -/
  wrMode   : String := "READ_FIRST"
  image    : Nat → Nat → Bool := fun _ _ => false
  /-- set bits in the primitive's `INIT*` parameters (for the report). -/
  initOnes : Nat := 0
deriving Inhabited

private def conn (c : Cell) (p : String) : Array SigBit := (c.conn? p).getD #[]

private def slicePins (a : Array SigBit) (lo n : Nat) : Array SigBit :=
  Array.ofFn (n := n) fun i => a[lo + i.val]?.getD .undef

/-! ### Distributed RAM (`RAM32M`, `RAM64M`)

yosys uses these two shapes, and the netlist says which:

* **lanes** — ports `A`/`B`/`C` are three *data lanes* of one array, so
  `DIA`/`DIB`/`DIC` are different nets and `ADDRA = ADDRB = ADDRC` is the
  single read address. Lane order is `C` (low), `B`, `A` (high).
* **replicas** — ports `A`/`B`/`C`(`/D`) are *read ports* of replicated
  content, so `DIA = DIB = DIC` and the addresses differ.

`ADDRD` is the write address in both shapes (it is the primitive's write
port). A cell matching neither shape is an error naming it. -/
private def lutramIface (c : Cell) (depth : Nat) : Except String CellIface := do
  let dia := conn c "DIA"; let dib := conn c "DIB"; let dic := conn c "DIC"
  let did := conn c "DID"
  let aw := if depth == 32 then 5 else 6
  let pw := dia.size
  if pw == 0 then throw s!"{c.type} '{c.name}': DIA is unconnected"
  let wrAddr := slicePins (conn c "ADDRD") 0 aw
  let init := fun (p : String) => (c.param? p).getD ""
  let replicated := dib == dia && (dic.isEmpty || dic == dia) && (did.isEmpty || did == dia)
  if replicated then
    -- One content bit lane per cell; each port is an independent read port.
    let mut rd : Array (Array SigBit × Array SigBit) := #[]
    for (ap, dp) in [("ADDRA", "DOA"), ("ADDRB", "DOB"), ("ADDRC", "DOC")] do
      let d := conn c dp
      unless d.isEmpty do rd := rd.push (slicePins (conn c ap) 0 aw, d)
    pure { name := c.name, ty := c.type, family := .lutram, depth := depth,
           width := pw, wrAddr := wrAddr, wrEn := conn c "WE",
           wrClk := conn c "WCLK", wrData := dia, rdPorts := rd,
           syncRead := false,
           image := fun a j => paramBit (init "INIT_A") (a * pw + j),
           initOnes := paramOnes (init "INIT_A") }
  else
    let addrA := slicePins (conn c "ADDRA") 0 aw
    unless slicePins (conn c "ADDRB") 0 aw == addrA && slicePins (conn c "ADDRC") 0 aw == addrA do
      throw s!"{c.type} '{c.name}': DIA/DIB/DIC differ (three data lanes) but \
        the read addresses ADDRA/ADDRB/ADDRC are not the same net — the \
        checker does not model this mixed lane/replica shape"
    unless dib.size == pw && dic.size == pw do
      throw s!"{c.type} '{c.name}': data lanes DIA/DIB/DIC have different widths"
    let ports := ["INIT_C", "INIT_B", "INIT_A"]
    pure { name := c.name, ty := c.type, family := .lutram, depth := depth,
           width := 3 * pw, wrAddr := wrAddr, wrEn := conn c "WE",
           wrClk := conn c "WCLK", wrData := dic ++ dib ++ dia,
           rdPorts := #[(addrA, conn c "DOC" ++ conn c "DOB" ++ conn c "DOA")],
           syncRead := false,
           image := fun a j =>
             paramBit (init (ports[j / pw]!)) (a * pw + j % pw),
           initOnes := paramOnes (init "INIT_A") + paramOnes (init "INIT_B")
                       + paramOnes (init "INIT_C") }

/-! ### Block RAM (`RAMB18E1`, `RAMB36E1`)

The configured word is `w` bits laid out as `w/9` groups of nine: eight
data bits then one parity bit. Data bit `d` of the cell's array lives in
`INIT_{d/256}` at bit `d%256`, parity bit `p` in `INITP_{p/256}`; the pins
split the same word across `DIADI`/`DIBDI` (data) and `DIPADIP`/`DIPBDIP`
(parity) at the widths the JSON reports. `SDP` writes on port B and reads
on port A with the full width; `TDP` here is width-`w` write on A, read on
B. Any other mode is an error naming the cell. -/
private def hexDigit (n : Nat) : String :=
  let d := fun (k : Nat) => "0123456789ABCDEF".toList[k]!
  String.ofList [d (n / 16), d (n % 16)]

private def bramIface (c : Cell) : Except String CellIface := do
  let is36 := c.type == "RAMB36E1" || c.type == "RAMB36"
  let totalData := if is36 then 32768 else 16384
  -- Address pins are 16 (RAMB36) / 14 (RAMB18) wide with ADDR[14:0] /
  -- ADDR[13:0] usable; the word address sits in the TOP `addrBits` of that.
  let usable := if is36 then 15 else 14
  let mode := (c.param? "RAM_MODE").getD "TDP"
  let pnat := fun p => (c.param? p).bind paramNat |>.getD 0
  let (wr, w) :=
    if mode == "SDP" then ("B", pnat "WRITE_WIDTH_B")
    else if pnat "WRITE_WIDTH_A" > 0 then ("A", pnat "WRITE_WIDTH_A")
    else ("B", pnat "WRITE_WIDTH_B")
  if w == 0 || w % 9 != 0 then
    throw s!"{c.type} '{c.name}': write width {w} (RAM_MODE {mode}) is not a \
      multiple of 9 — the checker models only the byte-plus-parity widths \
      (9/18/36/72) synth_xilinx emits for a Loom memory"
  let dpw := w - w / 9          -- data bits per word
  let ppw := w / 9              -- parity bits per word
  let depth := totalData / dpw
  let addrBits := Nat.log2 depth
  if 2 ^ addrBits != depth then
    throw s!"{c.type} '{c.name}': derived depth {depth} is not a power of two"
  let lowBit := usable - addrBits
  -- Pins. In SDP the single read port is A and carries the whole word on
  -- DOADO+DOPADOP+DOBDO+DOPBDOP; the write is B, likewise across all four.
  let (wrAddrPin, wrEnPin, wrClkPin, rdAddrPin, _rdClkPin) :=
    if wr == "B" then
      ("ADDRBWRADDR", "WEBWE", "CLKBWRCLK", "ADDRARDADDR", "CLKARDCLK")
    else ("ADDRARDADDR", "WEA", "CLKARDCLK", "ADDRBWRADDR", "CLKBWRCLK")
  let assemble := fun (dA dB pA pB : String) =>
    let da := conn c dA; let pa := conn c pA
    Array.ofFn (n := w) fun j =>
      let g := j.val / 9; let r := j.val % 9
      if r == 8 then
        (if g < pa.size then pa[g]? else (conn c pB)[g - pa.size]?).getD .undef
      else
        let d := 8 * g + r
        (if d < da.size then da[d]? else (conn c dB)[d - da.size]?).getD .undef
  let wrData :=
    if mode == "SDP" then assemble "DIADI" "DIBDI" "DIPADIP" "DIPBDIP"
    else if wr == "A" then assemble "DIADI" "DIADI" "DIPADIP" "DIPADIP"
    else assemble "DIBDI" "DIBDI" "DIPBDIP" "DIPBDIP"
  let rdData :=
    if mode == "SDP" then assemble "DOADO" "DOBDO" "DOPADOP" "DOPBDOP"
    else if wr == "A" then assemble "DOBDO" "DOBDO" "DOPBDOP" "DOPBDOP"
    else assemble "DOADO" "DOADO" "DOPADOP" "DOPADOP"
  -- The configuration image.
  let bit := fun (pre : String) (rows : Nat) (idx : Nat) =>
    if idx / 256 ≥ rows then false
    else paramBit ((c.param? s!"{pre}_{hexDigit (idx / 256)}").getD "") (idx % 256)
  let dRows := if is36 then 128 else 64
  let pRows := if is36 then 16 else 8
  let mut ones := 0
  for (k, v) in c.params do
    if k.startsWith "INIT_" || k.startsWith "INITP_" then ones := ones + paramOnes v
  pure { name := c.name, ty := c.type, family := .bram, depth := depth,
         width := w,
         wrAddr := slicePins (conn c wrAddrPin) lowBit addrBits,
         wrEn := conn c wrEnPin, wrClk := conn c wrClkPin,
         wrData := wrData,
         rdPorts := #[(slicePins (conn c rdAddrPin) lowBit addrBits, rdData)],
         syncRead := true,
         regOut := ((c.param? "DOA_REG").bind paramNat |>.getD 0) != 0
                   || ((c.param? "DOB_REG").bind paramNat |>.getD 0) != 0,
         wrMode := (c.param? (if wr == "A" then "WRITE_MODE_A" else "WRITE_MODE_B")).getD "?",
         image := fun a j =>
           let g := j / 9; let r := j % 9
           if r == 8 then bit "INITP" pRows (a * ppw + g)
           else bit "INIT" dRows (a * dpw + 8 * g + r),
         initOnes := ones }

/-- Resolve one memory primitive. Unsupported *shapes* of a supported cell
type are errors naming the cell — never skips. -/
def cellIface (c : Cell) : Except String CellIface :=
  if c.type == "RAM32M" || c.type == "RAM32M16" then lutramIface c 32
  else if c.type == "RAM64M" || c.type == "RAM64M8" then lutramIface c 64
  else if (memFamily c.type) == some .bram then bramIface c
  else throw s!"memory primitive '{c.type}' (instance '{c.name}') has no \
    interface model — the checker cannot state what it stores, so it will \
    not pretend to have checked it"

/-! ## Banks: the primitives of one µVerilog memory -/

/-- `dmem.0.0`, `u_dual.ep_cell_flags.0.7` ↦ the memory's name: yosys names
a mapped memory's primitives `<mem>.<group>.<index>`. -/
def memBankOf (cellName : String) : String :=
  let parts := (cellName.splitOn ".").reverse
  let rec strip : List String → List String
    | [] => []
    | [x] => [x]
    | x :: xs => if x != "" && x.all Char.isDigit then strip xs else x :: xs
  ((strip parts).head?).getD cellName

/-- The `(group, index)` suffix of a primitive's name, for the numeric sort
(`x.0.10` must follow `x.0.2`). -/
def memCellIdx (cellName : String) : Nat × Nat :=
  let parts := (cellName.splitOn ".").reverse
  let num := fun (s : String) => (s.toNat?).getD 0
  match parts with
  | b :: g :: _ => (num g, num b)
  | [b] => (0, num b)
  | [] => (0, 0)

/-- A µVerilog memory as the netlist realizes it: a grid of primitives
`nRepl × nDepth × nLane`. Replicas hold identical content for independent
read ports; depth groups split the address space; lanes split the word. -/
structure Bank where
  mem     : String
  cells   : Array CellIface
  family  : MemFamily
  nRepl   : Nat
  nDepth  : Nat
  nLane   : Nat
  /-- addresses per cell, bits per cell -/
  cellDepth : Nat
  cellWidth : Nat
deriving Inhabited

/-- `cells[r][g][l]`, i.e. the primitive holding lane `l` of depth group
`g` in replica `r`, under the arrangement derived from yosys's naming. -/
def Bank.at (b : Bank) (r g l : Nat) : Option CellIface :=
  b.cells[r * (b.nDepth * b.nLane) + g * b.nLane + l]?

/-- Assemble the primitives named for one µVerilog memory into a bank.
Every arithmetic assumption here (the grid shape, the arrangement) is only
a *hint*: `Tools/EqCheck.lean` then miters each cell's pins against the IR
expression the hint predicts, so a wrong hint is a loud failure, never a
silent pass. -/
def buildBank (mem : String) (memDepth memWidth : Nat) (cs : Array Cell) :
    Except String Bank := do
  let sorted := cs.qsort (fun a b =>
    let x := memCellIdx a.name; let y := memCellIdx b.name
    x.1 < y.1 || (x.1 == y.1 && x.2 < y.2))
  let ifaces ← sorted.mapM cellIface
  let some head := ifaces[0]?
    | throw s!"memory '{mem}': no primitives"
  for i in ifaces do
    unless i.depth == head.depth && i.width == head.width && i.ty == head.ty do
      throw s!"memory '{mem}': primitive '{i.name}' ({i.ty}, {i.depth}×{i.width}) \
        does not match '{head.name}' ({head.ty}, {head.depth}×{head.width}) — \
        the checker does not model a bank built from unequal primitives"
  let nDepth := (memDepth + head.depth - 1) / head.depth
  let nLane := (memWidth + head.width - 1) / head.width
  let per := nDepth * nLane
  if per == 0 || ifaces.size % per != 0 then
    throw s!"memory '{mem}': {ifaces.size} primitives do not divide into \
      {nDepth} depth group(s) × {nLane} lane(s) of {head.ty}"
  let nRepl := ifaces.size / per
  -- Structural cross-check of the arrangement: cells the hint puts in the
  -- same depth group must share a write-enable net, and different groups
  -- must not (a depth split is exactly a per-group enable).
  for r in [0:nRepl] do
    for g in [0:nDepth] do
      let some c0 := ifaces[r * per + g * nLane]? | throw s!"memory '{mem}': short bank"
      for l in [0:nLane] do
        let some c := ifaces[r * per + g * nLane + l]? | throw s!"memory '{mem}': short bank"
        unless c.wrEn == c0.wrEn do
          throw s!"memory '{mem}': '{c.name}' and '{c0.name}' should be lanes of \
            one depth group but have different write-enable nets — the bank's \
            layout is not what this checker derived from the cell names"
  pure { mem := mem, cells := ifaces, family := head.family, nRepl := nRepl,
         nDepth := nDepth, nLane := nLane, cellDepth := head.depth,
         cellWidth := head.width }

/-- The bank's configuration image: content bit `j` of address `a`, read
out of replica 0's `INIT*` parameters. -/
def Bank.image (b : Bank) (a j : Nat) : Bool :=
  match b.at 0 (a / b.cellDepth) (j / b.cellWidth) with
  | none => false
  | some c => c.image (a % b.cellDepth) (j % b.cellWidth)

/-- Total set bits across every primitive's `INIT*` parameters. -/
def Bank.initOnes (b : Bank) : Nat := b.cells.foldl (fun n c => n + c.initOnes) 0

/-! ## The reset image

The declared image is `MemDef.init`; the realized one is `Bank.image`. Two
things are checked, and they are different claims:

1. **fidelity** — the primitives' `INIT*` parameters encode exactly the
   declared image (`x`, an uninitialized location, reads as the `0` the
   fabric delivers);
2. **deliverability** — a non-zero image on a `RAM*` (distributed) bank is
   a FAILURE even when the netlist's `INIT*` is faithful, because the
   configuration path does not carry it to the fabric. That is D30, and it
   is the only one of the two that fires on the pre-fix epoch netlist under
   yosys 0.33: 0.33 writes the `RAM64M` image faithfully into the JSON and
   the bank still comes up all-zero on the board. -/
inductive ImageVerdict where
  | ok (nonZero : Bool)
  | mismatch (addr bit : Nat) (declared realized : Bool)
  | undelivered (family : MemFamily) (ty : String) (cell : String)
deriving Inhabited

def checkImage (b : Bank) (m : MemDef) : ImageVerdict := Id.run do
  let mut nonZero := false
  let mut bad : Option (Nat × Nat × Bool × Bool) := none
  for a in [0:2 ^ m.addrWidth] do
    let w := m.init a
    for j in [0:m.dataWidth] do
      let d := w.getLsbD j
      if d then nonZero := true
      if bad.isNone && d != b.image a j then bad := some (a, j, d, b.image a j)
  match bad with
  | some (a, j, d, r) => return .mismatch a j d r
  | none =>
      -- The deliverability rule is `Loom.Hw.imageDelivered`, shared
      -- verbatim with the design-level D37 check; only the *source* of the
      -- family differs (observed here, predicted there).
      if !imageDelivered b.family nonZero then
        let c := b.cells[0]!
        return .undelivered b.family c.ty c.name
      return .ok nonZero

end Loom.Netlist
