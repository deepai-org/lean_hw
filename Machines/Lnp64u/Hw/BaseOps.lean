import Machines.Lnp64u.Hw.Enc
import Machines.Lnp64u.Isa

/-!
# LNP64-µ core: shared circuits (task 1.11)

The circuit pieces every rule shares: `isa`-derived opcode/cost tables,
architectural register read/write (`r0` hardwired — the register is simply
never written, so reading it is reading zero), the `domCovers` OR-tree over
region registers, the `haltWith` circuit (halt + cause + gate unwind, the
T6 no-hostage path), and the in-flight word's D1 bit fields.

Spec-fidelity notes:
* Retirement (in `SysOps.lean`) mirrors `Step.retire` exactly: `pc`
  advances on every non-faulting outcome; a **fault** leaves `pc` at the
  faulting instruction (the spec's fault arm runs `haltWith` on the
  *pre-advance* state).
* Opcode dispatch is keyed by mnemonic through `isa`, so opcode numbers,
  validity, and WCET costs stay in sync with the spec by construction.
-/

namespace Machines.Lnp64u.Hw

open Loom.Hw

/-! ## `isa`-derived tables -/

/-- Opcode of a mnemonic (63 = unused encoding if the mnemonic is unknown;
never happens for the names used below). -/
def opcodeOf (mn : String) : BitVec 6 :=
  ((isa.toList.find? (·.mnemonic = mn)).map (·.opcode)).getD 63

/-- `(opcode, WCET cost)` for every declared instruction. -/
def opCosts : List (BitVec 6 × Nat) :=
  isa.toList.map fun i => (i.opcode, i.cost.cost)

/-- Does `opc` decode (i.e. name a declared instruction)? -/
def knownE (opc : Expr 6) : Expr 1 :=
  orAll (opCosts.map fun (o, _) => .eq opc (.lit o))

/-- The issue-time WCET charge of `opc` (8 bits; all costs ≤ 24). -/
def costE (opc : Expr 6) : Expr 8 :=
  opCosts.foldr
    (fun (o, c) acc => .mux (.eq opc (.lit o)) (.lit (BitVec.ofNat 8 c)) acc)
    (.lit 0)

/-! ## Shared circuit pieces -/

def rPc (d : DomainId) : Expr 12 := .reg 12 (dpc d)

/-- Architectural register read at a dynamic index (`r0` register is never
written, so it reads zero — the spec's `DomainState.reg`). -/
def readReg (d : DomainId) (r : Expr 3) : Expr 32 :=
  muxFin (fun i => .reg 32 (dreg d i)) r

/-- Architectural register write at a dynamic index; writes to `r0`
discarded (the spec's `DomainState.setReg`). -/
def writeReg (d : DomainId) (r : Expr 3) (v : Expr 32) : Act :=
  seqAll <| (List.finRange numRegs).filterMap fun i =>
    if i.val = 0 then none
    else some (.ite (.eq r (.lit (BitVec.ofNat 3 i.val)))
      (.write 32 (dreg d i) v) .skip)

/-- Does region register `r` of domain `d` cover `a` with `need`
(`Region.covers`: base ≤ a < base + len, 14-bit compare so the sum cannot
wrap, plus the static permission mask)? -/
def coversE (d : DomainId) (r : RegionId) (a : Expr 12) (need : Perms) :
    Expr 1 :=
  let rg : Expr 42 := .reg 42 (drgn d r)
  let base : Expr 12 := field rg 16 12
  let len : Expr 13 := field rg 3 13
  let permOk : List (Expr 1) :=
    (if need.r then [field rg 0 1] else []) ++
    (if need.w then [field rg 1 1] else []) ++
    (if need.x then [field rg 2 1] else [])
  andAll <|
    [.reg 1 (drgnV d r),
     .not (.ult a base),
     .ult (.zext a 14) (.add (.zext base 14) (.zext len 14))] ++ permOk

/-- `MachineState.domCovers`: OR over the domain's region registers. -/
def domCoversE (d : DomainId) (a : Expr 12) (need : Perms) : Expr 1 :=
  orAll ((List.finRange numRegions).map fun r => coversE d r a need)

/-- The `haltWith` circuit (`Kernel.haltDom`): run := halted, cause set,
serving := none; if `d` was serving a gate with a live activation, the gate
frees and the caller resumes running with `-ECALLEEFAULT` in its reply
register (write order = spec order: a self-caller ends up running). -/
def haltAct (d : DomainId) (cause : BitVec 32) : Act :=
  .seq (.write 2 (drun d) (.lit 1)) <|
  .seq (.write 32 (dcause d) (.lit cause)) <|
  .seq (.write 1 (dsrvV d) (.lit 0)) <|
  seqAll <| (List.finRange numGates).map fun g =>
    .ite (andAll [.reg 1 (dsrvV d),
                  .eq (.reg 2 (dsrv d)) (.lit (BitVec.ofNat 2 g.val)),
                  .reg 1 (gactV g)])
      (.seq (.write 1 (gactV g) (.lit 0))
        (seqAll <| (List.finRange numDomains).map fun c =>
          .ite (.eq (.reg 2 (gcaller g)) (.lit (BitVec.ofNat 2 c.val)))
            (.seq (.write 2 (drun c) (.lit 0))
              (writeReg c (.reg 3 (gcallerRd g)) (.lit Errno.calleeFault.toWord)))
            .skip))
      .skip

def haltFault (d : DomainId) (f : Fault) : Act :=
  haltAct d (BitVec.ofNat 32 f.code)

/-! ## In-flight word fields (D1 layout; retirement lives in `SysOps.lean`) -/

def ifWord : Expr 32 := .reg 32 "if_word"
def opcE : Expr 6 := field ifWord 0 6
def rdE : Expr 3 := field ifWord 6 3
def rs1E : Expr 3 := field ifWord 9 3
def rs2E : Expr 3 := field ifWord 12 3
def immE : Expr 17 := field ifWord 15 17
/-- Sign-extended immediate (`immExt`). -/
def immX : Expr 32 := .sext immE 32

end Machines.Lnp64u.Hw
