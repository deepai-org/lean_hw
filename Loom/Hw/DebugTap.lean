-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Declarations
import Loom.Hw.ReadsOk

/-!
# Lightweight, explicitly unverified debug taps

`DebugMap` is the escape hatch for short-lived board probes. It generates the
repetitive Verilog between an emitted design and a BSCAN read mux: source
selection, optional first-event capture, two-flop DRCK sampling, and address
decode. Adding a probe changes one Lean list and regenerates one include; it
does not add ISS state or lockstep obligations.

Typed register probes and register-only `Expr` probes derive their child-port
dependencies. Raw wrapper expressions remain available for values outside the
EDSL; internal memory reads are rejected until the child module has an explicit
debug-only export mechanism.

This is intentionally *not* part of `Design` semantics or the compiler
correctness theorem. Raw Verilog expressions, asynchronous sampling, and the
board wrapper remain external instrumentation. `DebugMap.report` names that
boundary rather than presenting a debug observation as a theorem.
-/

namespace Loom.Hw

/-- How the wrapper obtains the value exposed by a debug tap. -/
inductive DebugTapMode where
  /-- Continuously sample the named source through a two-flop DRCK crossing. -/
  | level
  /-- In `sysclk`, capture the first value for which the per-core trigger is
  true; clear both captured values and valid bits when `reset` is true. -/
  | sticky (trigger0 trigger1 reset : String)
  deriving Repr, BEq

/-- One child-register dependency of a typed debug expression. -/
structure DebugPort where
  name : String
  width : Nat
  deriving Repr, BEq

/-- One logical debug value. Values wider than 32 bits occupy consecutive
BSCAN words beginning at `base`. Raw taps place Verilog in `source0` and
`source1`; typed taps use generated child-output wires and may also carry a
generated combinational preamble. -/
structure DebugTap where
  base : Nat
  name : String
  width : Nat
  source0 : String
  source1 : String
  /-- Empty for a raw wrapper expression. A typed tap lists each source
  register once; the generator declares and connects both cores' ports. -/
  ports : List DebugPort := []
  /-- Wrapper-local combinational wires generated for a typed expression.
  `__LOOM_TAP__` is replaced by the map index during rendering. -/
  preamble0 : String := ""
  preamble1 : String := ""
  /-- False records an unsupported typed expression (currently a memory read)
  so `DebugMap.okB` fails closed instead of emitting a bogus observation. -/
  sourceValid : Bool := true
  mode : DebugTapMode := .level
  /-- Raise the generated per-core halt request after this sticky tap first
  fires. The request remains asserted until the tap's reset clears `valid`. -/
  haltOnTrigger : Bool := false
  deriving Repr, BEq

namespace DebugTap

def words (tap : DebugTap) : Nat := (tap.width + 31) / 32

def addresses (tap : DebugTap) : List Nat :=
  (List.range tap.words).map (tap.base + ·)

def outputNames (tap : DebugTap) : List String :=
  tap.ports.flatMap fun port => [s!"c0_{port.name}", s!"c1_{port.name}"]

private def placeholder : String := "__LOOM_TAP__"

private def sourceWire (port core : Nat) : String :=
  s!"loom_debug_source_{placeholder}_p{port}_c{core}"

/-- A typed register exported by both halves of a composed dual design.
The generated include declares local wires and connects the existing child
output ports. -/
def ofDualReg {w : Nat} (base : Nat) (reg : Reg w) : DebugTap :=
  { base, name := reg.name, width := w
    source0 := sourceWire 0 0
    source1 := sourceWire 0 1
    ports := [{ name := reg.name, width := w }] }

/-- The low BSCAN word of a typed dual-core register. Useful for wide traces
when board bring-up needs the low address/value word only. -/
def lowWordOfDualReg {w : Nat} (base : Nat) (reg : Reg w) : DebugTap :=
  let width := min w 32
  { base, name := s!"{reg.name}_lo", width
    source0 := s!"{sourceWire 0 0}[{width - 1}:0]"
    source1 := s!"{sourceWire 0 1}[{width - 1}:0]"
    ports := [{ name := reg.name, width := w }] }

private structure ExprRenderState where
  lines : Array String := #[]
  next : Nat := 0
  valid : Bool := true

private def portIndex? (name : String) (width : Nat) : List DebugPort → Option Nat
  | [] => none
  | port :: ports =>
      if port.name = name && port.width = width then some 0
      else (portIndex? name width ports).map (· + 1)

private def freshExprWire (core width : Nat) (rhs : String) : StateM ExprRenderState String := do
  let st ← get
  let wire := s!"loom_debug_expr_{placeholder}_c{core}_n{st.next}"
  set { st with next := st.next + 1
                lines := st.lines.push s!"wire [{width - 1}:0] {wire} = {rhs};" }
  pure wire

private def renderExpr (ports : List DebugPort) (core : Nat) :
    {w : Nat} → Expr w → StateM ExprRenderState String
  | w, .lit v => freshExprWire core w s!"{w}'d{v.toNat}"
  | w, .reg _ name =>
      match portIndex? name w ports with
      | some index => pure (sourceWire index core)
      | none => do
          modify fun st => { st with valid := false }
          freshExprWire core w s!"{w}'d0 /* undeclared debug dependency */"
  | dw, .memRead _ _ _ => do
      modify fun st => { st with valid := false }
      freshExprWire core dw s!"{dw}'d0 /* memory debug expressions unsupported */"
  | w, .and a b => do freshExprWire core w s!"({← renderExpr ports core a}) & ({← renderExpr ports core b})"
  | w, .or a b => do freshExprWire core w s!"({← renderExpr ports core a}) | ({← renderExpr ports core b})"
  | w, .xor a b => do freshExprWire core w s!"({← renderExpr ports core a}) ^ ({← renderExpr ports core b})"
  | w, .not a => do freshExprWire core w s!"~({← renderExpr ports core a})"
  | w, .add a b => do freshExprWire core w s!"({← renderExpr ports core a}) + ({← renderExpr ports core b})"
  | w, .sub a b => do freshExprWire core w s!"({← renderExpr ports core a}) - ({← renderExpr ports core b})"
  | w, .shl a b => do freshExprWire core w s!"({← renderExpr ports core a}) << ({← renderExpr ports core b})"
  | w, .shr a b => do freshExprWire core w s!"({← renderExpr ports core a}) >> ({← renderExpr ports core b})"
  | _, .eq a b => do freshExprWire core 1 s!"({← renderExpr ports core a}) == ({← renderExpr ports core b})"
  | _, .ult a b => do freshExprWire core 1 s!"({← renderExpr ports core a}) < ({← renderExpr ports core b})"
  | _, .slt a b => do freshExprWire core 1 s!"$signed({← renderExpr ports core a}) < $signed({← renderExpr ports core b})"
  | w, .mux c t f => do
      freshExprWire core w s!"({← renderExpr ports core c}) ? ({← renderExpr ports core t}) : ({← renderExpr ports core f})"
  | _, @Expr.slice _ a lo width => do
      freshExprWire core width s!"{← renderExpr ports core a}[{lo + width - 1}:{lo}]"
  | width, @Expr.zext w a _ => do
      let source ← renderExpr ports core a
      if width > w then
        freshExprWire core width ("{" ++ s!"{width - w}'d0, {source}" ++ "}")
      else if width = w then freshExprWire core width source
      else freshExprWire core width s!"{source}[{width - 1}:0]"
  | width, @Expr.sext w a _ => do
      let source ← renderExpr ports core a
      if width > w then
        freshExprWire core width ("{" ++ s!"{width - w}" ++ "{" ++
          s!"{source}[{w - 1}]" ++ "}}, " ++ source ++ "}")
      else if width = w then freshExprWire core width source
      else freshExprWire core width s!"{source}[{width - 1}:0]"

private def renderedExpr {w : Nat} (ports : List DebugPort) (core : Nat)
    (expr : Expr w) : String × String × Bool :=
  let (root, st) := (renderExpr ports core expr).run {}
  (String.join (st.lines.toList.map (· ++ "\n")), root, st.valid)

/-- A register-only typed EDSL expression over both cores. Loom derives every
child output dependency and emits the wrapper expression; no raw Verilog is
written at the call site. Memory reads fail the map guard because memories are
not child ports. -/
def ofDualExpr {w : Nat} (base : Nat) (name : String) (expr : Expr w) : DebugTap :=
  let ports := expr.readSites.1.eraseDups.map fun (n, width) => ({ name := n, width } : DebugPort)
  let (preamble0, source0, valid0) := renderedExpr ports 0 expr
  let (preamble1, source1, valid1) := renderedExpr ports 1 expr
  { base, name, width := w, source0, source1, ports, preamble0, preamble1
    sourceValid := valid0 && valid1 && expr.readSites.2.isEmpty }

/-- First-event capture of a typed one-bit impossible-state predicate. The
predicate itself is both trigger and captured value, so the readback remains
one after the first hit until reset. -/
def stickyOfDualPredicate (base : Nat) (name : String) (predicate : Expr 1)
    (reset : String := "rst") (haltOnTrigger : Bool := false) : DebugTap :=
  let tap := ofDualExpr base name predicate
  { tap with mode := .sticky tap.source0 tap.source1 reset, haltOnTrigger }

/-- A raw continuously sampled expression. This is the one-line escape hatch
for a temporary combinational observation outside the EDSL. -/
def raw (base : Nat) (name : String) (width : Nat)
    (source0 source1 : String) : DebugTap :=
  { base, name, width, source0, source1 }

/-- A raw first-event capture implemented entirely in the board wrapper.
It is suitable for an ephemeral "this should never happen" latch without
adding a register to the EDSL, ISS, or lockstep comparator. -/
def stickyRaw (base : Nat) (name : String) (width : Nat)
    (trigger0 value0 trigger1 value1 : String) (reset : String := "rst")
    (haltOnTrigger : Bool := false) : DebugTap :=
  { base, name, width, source0 := value0, source1 := value1
    mode := .sticky trigger0 trigger1 reset, haltOnTrigger }

end DebugTap

/-- A generated BSCAN read-map fragment. The surrounding wrapper convention
provides `sysclk`, `drck`, `rst`, and `w_core`; the generated function is named
`loom_debug_read`. -/
structure DebugMap where
  name : String
  taps : List DebugTap
  /-- Child outputs already connected by the handwritten wrapper. Typed taps
  reuse wrapper wires named `o_c0_<name>`/`o_c1_<name>` instead of emitting a
  second named-port binding. -/
  existingPorts : List DebugPort := []
  deadValue : Nat := 0xDEAD0000
  deriving Repr, BEq

namespace DebugMap

def addresses (m : DebugMap) : List Nat := m.taps.flatMap (·.addresses)

private structure PortUse where
  tapIndex : Nat
  portIndex : Nat
  port : DebugPort

private def portUses (m : DebugMap) : List PortUse :=
  m.taps.zipIdx.flatMap fun (tap, tapIndex) =>
    tap.ports.zipIdx.map fun (port, portIndex) => { tapIndex, portIndex, port }

private def samePort (a b : DebugPort) : Bool :=
  a.name = b.name && a.width = b.width

private def localPortWire (use : PortUse) (core : Nat) : String :=
  s!"loom_debug_source_{use.tapIndex}_p{use.portIndex}_c{core}"

private def canonicalUse? (m : DebugMap) (port : DebugPort) : Option PortUse :=
  m.portUses.find? fun use => samePort use.port port

private def isExisting (m : DebugMap) (port : DebugPort) : Bool :=
  m.existingPorts.any fun existing => samePort existing port

def sourceOk (tap : DebugTap) : Bool :=
  tap.sourceValid && !tap.source0.isEmpty && !tap.source1.isEmpty &&
  match tap.mode with
  | .level => !tap.haltOnTrigger
  | .sticky trigger0 trigger1 reset =>
      !trigger0.isEmpty && !trigger1.isEmpty && !reset.isEmpty

private def portOk (design : Design) (port : DebugPort) : Bool :=
  let outputOk (name : String) := design.regs.any fun reg =>
    reg.name = name && reg.width = port.width && design.outputs.contains name
  port.width > 0 && outputOk s!"c0_{port.name}" && outputOk s!"c1_{port.name}"

private def portsOk (design : Design) (tap : DebugTap) : Bool :=
  (tap.ports.map (·.name)).Nodup && tap.ports.all (portOk design) &&
  tap.outputNames.all design.outputs.contains

/-- Executable guard: nonempty/unique taps, 1..128-bit addresses, unique BSCAN
words, nonempty raw expressions, and all typed-port references exported by the
design being wrapped. -/
def okB (m : DebugMap) (design : Design) : Bool :=
  !m.taps.isEmpty &&
  m.taps.all (fun tap => !tap.name.isEmpty && tap.width > 0 &&
    tap.base + tap.words ≤ 128 && sourceOk tap && portsOk design tap) &&
  (m.taps.map (·.name)).Nodup && m.addresses.Nodup &&
  (m.existingPorts.map (·.name)).Nodup && m.existingPorts.all (portOk design)

def report (m : DebugMap) : String :=
  let words := m.addresses.length
  let typed := m.taps.filter (fun tap => !tap.ports.isEmpty) |>.length
  let sticky := m.taps.filter (fun tap => match tap.mode with
    | .sticky .. => true | .level => false) |>.length
  let halting := m.taps.filter (·.haltOnTrigger) |>.length
  s!"debug map '{m.name}': taps={m.taps.length} words={words} typed={typed} sticky={sticky} halting={halting}\n\
TRUST: instrumentation only; raw expressions, CDC sampling, wrapper integration, and observed values are outside the Design/compiler theorem"

private def widthDecl (width : Nat) : String := s!"[{width - 1}:0]"

private def instantiate (index : Nat) (source : String) : String :=
  source.replace DebugTap.placeholder (toString index)

private def renderCapture (index : Nat) (tap : DebugTap) : String :=
  match tap.mode with
  | .level => ""
  | .sticky trigger0 trigger1 reset =>
      let source0 := instantiate index tap.source0
      let source1 := instantiate index tap.source1
      let trigger0 := instantiate index trigger0
      let trigger1 := instantiate index trigger1
      s!"reg {widthDecl tap.width} loom_debug_hold_{index}_c0 = {tap.width}'d0;\n\
reg {widthDecl tap.width} loom_debug_hold_{index}_c1 = {tap.width}'d0;\n\
reg loom_debug_valid_{index}_c0 = 1'b0;\n\
reg loom_debug_valid_{index}_c1 = 1'b0;\n\
always @(posedge sysclk) begin\n\
  if ({reset}) begin\n\
    loom_debug_hold_{index}_c0 <= {tap.width}'d0; loom_debug_valid_{index}_c0 <= 1'b0;\n\
    loom_debug_hold_{index}_c1 <= {tap.width}'d0; loom_debug_valid_{index}_c1 <= 1'b0;\n\
  end else begin\n\
    if (!loom_debug_valid_{index}_c0 && ({trigger0})) begin\n\
      loom_debug_hold_{index}_c0 <= {source0}; loom_debug_valid_{index}_c0 <= 1'b1;\n\
    end\n\
    if (!loom_debug_valid_{index}_c1 && ({trigger1})) begin\n\
      loom_debug_hold_{index}_c1 <= {source1}; loom_debug_valid_{index}_c1 <= 1'b1;\n\
    end\n\
  end\n\
end\n"

private def captureSource (index : Nat) (core : Nat) (tap : DebugTap) : String :=
  match tap.mode with
  | .level =>
      instantiate index (if core = 0 then tap.source0 else tap.source1)
  | .sticky .. => s!"loom_debug_hold_{index}_c{core}"

private def renderTypedWire (m : DebugMap) (use : PortUse) : String :=
  let wire0 := localPortWire use 0
  let wire1 := localPortWire use 1
  if m.isExisting use.port then
    s!"wire {widthDecl use.port.width} {wire0} = o_c0_{use.port.name};\n\
wire {widthDecl use.port.width} {wire1} = o_c1_{use.port.name};\n"
  else match m.canonicalUse? use.port with
    | some canonical =>
        if canonical.tapIndex = use.tapIndex && canonical.portIndex = use.portIndex then
          s!"wire {widthDecl use.port.width} {wire0};\n\
wire {widthDecl use.port.width} {wire1};\n"
        else
          s!"wire {widthDecl use.port.width} {wire0} = {localPortWire canonical 0};\n\
wire {widthDecl use.port.width} {wire1} = {localPortWire canonical 1};\n"
    | none => ""

private def renderTypedWires (m : DebugMap) : String :=
  String.join <| m.portUses.map (renderTypedWire m)

private def renderPortConnection (m : DebugMap) (use : PortUse) : String :=
  if m.isExisting use.port then ""
  else match m.canonicalUse? use.port with
    | some canonical =>
        if canonical.tapIndex = use.tapIndex && canonical.portIndex = use.portIndex then
          s!"  , .o_c0_{use.port.name}({localPortWire use 0})\n\
  , .o_c1_{use.port.name}({localPortWire use 1})\n"
        else ""
    | none => ""

private def renderPortConnections (m : DebugMap) : String :=
  String.join <| m.portUses.map (renderPortConnection m)

private def renderPreamble (index : Nat) (tap : DebugTap) : String :=
  instantiate index tap.preamble0 ++ instantiate index tap.preamble1

private def renderSampler (index : Nat) (tap : DebugTap) : String :=
  s!"// tap {index}: {tap.name} ({tap.width} bits, BSCAN {tap.base}..{tap.base + tap.words - 1})\n" ++
  renderPreamble index tap ++
  renderCapture index tap ++
  s!"reg {widthDecl tap.width} loom_debug_meta_{index}_c0 = {tap.width}'d0;\n\
reg {widthDecl tap.width} loom_debug_sync_{index}_c0 = {tap.width}'d0;\n\
reg {widthDecl tap.width} loom_debug_meta_{index}_c1 = {tap.width}'d0;\n\
reg {widthDecl tap.width} loom_debug_sync_{index}_c1 = {tap.width}'d0;\n\
always @(posedge drck) begin\n\
  loom_debug_meta_{index}_c0 <= {captureSource index 0 tap};\n\
  loom_debug_sync_{index}_c0 <= loom_debug_meta_{index}_c0;\n\
  loom_debug_meta_{index}_c1 <= {captureSource index 1 tap};\n\
  loom_debug_sync_{index}_c1 <= loom_debug_meta_{index}_c1;\n\
end\n\
wire {widthDecl tap.width} loom_debug_selected_{index} = w_core ?\n\
  loom_debug_sync_{index}_c1 : loom_debug_sync_{index}_c0;\n"

private def renderWord (index word : Nat) (tap : DebugTap) : String :=
  let lo := word * 32
  let bits := min 32 (tap.width - lo)
  let hi := lo + bits - 1
  let value := s!"loom_debug_selected_{index}[{hi}:{lo}]"
  let rhs := if bits = 32 then value else "{" ++ s!"{32 - bits}'d0, {value}" ++ "}"
  s!"      7'd{tap.base + word}: loom_debug_read = {rhs}; // {tap.name}[{hi}:{lo}]\n"

private def renderCases (index : Nat) (tap : DebugTap) : String :=
  String.join <| (List.range tap.words).map fun word => renderWord index word tap

private def renderHaltRequest (m : DebugMap) (core : Nat) : String :=
  let terms := m.taps.zipIdx.filterMap fun (tap, index) =>
    if tap.haltOnTrigger then some s!"loom_debug_valid_{index}_c{core}" else none
  let rhs := if terms.isEmpty then "1'b0" else String.intercalate " | " terms
  s!"wire loom_debug_halt_request_c{core} = {rhs};\n"

/-- Render a Verilog include for one wrapper. This is an external artifact,
not the output of the verified µVerilog printer. -/
def render (m : DebugMap) : String :=
  "// Generated by Loom.Hw.DebugMap — DO NOT HAND EDIT.\n" ++
  "// UNVERIFIED DEBUG INSTRUMENTATION: outside Design semantics/compiler theorem.\n" ++
  "`ifdef LOOM_DEBUG_PORTS\n" ++
  renderPortConnections m ++
  "`else\n" ++
  renderTypedWires m ++
  String.join ((m.taps.zipIdx).map fun (tap, index) => renderSampler index tap ++ "\n") ++
  renderHaltRequest m 0 ++ renderHaltRequest m 1 ++
  "function [31:0] loom_debug_read;\n" ++
  "  input [6:0] loom_debug_index;\n" ++
  "  begin\n" ++
  "    case (loom_debug_index)\n" ++
  String.join ((m.taps.zipIdx).map fun (tap, index) => renderCases index tap) ++
  s!"      default: loom_debug_read = 32'h{String.ofList (Nat.toDigits 16 m.deadValue)};\n" ++
  "    endcase\n" ++
  "  end\n" ++
  "endfunction\n" ++
  "`endif\n"

/-- Render the BOARD-SIDE reader for the same map: a Tcl include (sourced
after `jtag_lib.tcl`, which provides `rd`) with one `debug_<name>` proc per
tap — multi-word taps assembled from their consecutive BSCAN words — and a
`debug_read_all` that prints every tap. The wrapper decode and this reader
derive from ONE tap list, so the read map cannot drift from the hardware
(the hand-maintained era shipped a reader whose index 56 was shadowed by a
wrapper case and returned another register's bits as pc[63:32]). Reads are
core-0 views (`rd` leaves the region bit clear); the core-1 view needs a
region-bit `rd` variant first. -/
def renderTcl (m : DebugMap) : String :=
  let procs := String.join <| m.taps.map fun tap =>
    let words := (List.range tap.words).map (fun w => s!"[rd {tap.base + w}]")
    let assemble := match words with
      | [one] => s!"return {one}"
      | ws => Id.run do
          -- little-endian word order: base = bits 31:0
          let mut expr := "0"
          let mut sh := 0
          for w in ws do
            expr := s!"({expr}) | (({w}) << {sh})"
            sh := sh + 32
          return s!"return [expr \{{expr}}]"
    s!"proc debug_{tap.name} \{} \{ {assemble} }\n"
  let prints := String.join <| m.taps.map fun tap =>
    let fmtw := (tap.width + 3) / 4
    s!"  puts [format \{{tap.name} = 0x%0{fmtw}x} [debug_{tap.name}]]\n"
  "# Generated by Loom.Hw.DebugMap — DO NOT HAND EDIT.\n" ++
  "# Reader half of the BSCAN debug map; source test/jtag_lib.tcl first.\n" ++
  s!"# map '{m.name}', taps={m.taps.length}\n" ++
  procs ++
  "proc debug_read_all {} {\n" ++ prints ++ "}\n"

private def write (m : DebugMap) (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path m.render
  let tclPath := path.withExtension "tcl"
  IO.FS.writeFile tclPath m.renderTcl
  IO.println s!"{path} + {tclPath} written\n{m.report}"

/-- Emit without evaluating a design. Intended for a large map with an
adjacent kernel-checked `okB = true` theorem: Lean's strict evaluation would
otherwise construct the entire composed design merely to pass an erased proof
argument. The name is explicit because omitting that adjacent certificate is
an instrumentation-integrity error, though never a release-theorem error. -/
def emitUnchecked (m : DebugMap) (path : System.FilePath) : IO Unit :=
  m.write path

/-- Runtime-checked emission, convenient for small designs. -/
def emit (m : DebugMap) (design : Design) (path : System.FilePath) : IO Unit := do
  if !m.okB design then
    throw <| IO.userError s!"DebugMap.emit: invalid map '{m.name}' for design '{design.name}'"
  m.write path

end DebugMap

end Loom.Hw
