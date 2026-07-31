-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lean.Data.Json

/-!
# yosys `write_json` netlists (D22, post-synthesis equivalence check)

A minimal reader for the netlist interchange format `yosys write_json`
emits: modules → ports / cells / netnames, with every signal a list of
*signal bits* (a net id, or a constant `0`/`1`/`x`/`z`).

Nothing here is on any theorem's trusted path: the netlist is an artifact
produced by an untrusted external synthesizer, and this file is the
untrusted reader for it (`Loom/Netlist/EQCHECK_SPEC.md`).
-/

namespace Loom.Netlist

open Lean (Json)

/-- One bit of a signal: a net id, or a constant. -/
inductive SigBit where
  | zero | one | undef | highz
  | net (id : Nat)
deriving DecidableEq, Repr, Inhabited

instance : ToString SigBit where
  toString
    | .zero => "1'0" | .one => "1'1" | .undef => "1'x" | .highz => "1'z"
    | .net i => s!"net{i}"

/-- A cell instance: type, parameters (rendered as strings), and the net
lists connected to each port. -/
structure Cell where
  name   : String
  type   : String
  params : List (String × String) := []
  conns  : List (String × Array SigBit) := []
deriving Inhabited, Repr

def Cell.conn? (c : Cell) (p : String) : Option (Array SigBit) :=
  (c.conns.find? (fun kv => kv.1 == p)).map (·.2)

def Cell.param? (c : Cell) (p : String) : Option String :=
  (c.params.find? (fun kv => kv.1 == p)).map (·.2)

/-- A named net (`netnames` entry). -/
structure NetName where
  name : String
  bits : Array SigBit
deriving Inhabited, Repr

/-- A module port. -/
structure Port where
  name : String
  dir  : String
  bits : Array SigBit
deriving Inhabited, Repr

/-- A netlist module. -/
structure NlModule where
  name  : String
  ports : List Port
  cells : List Cell
  nets  : List NetName
deriving Inhabited

def NlModule.port? (m : NlModule) (n : String) : Option Port :=
  m.ports.find? (fun p => p.name == n)

def NlModule.net? (m : NlModule) (n : String) : Option NetName :=
  m.nets.find? (fun p => p.name == n)

/-! ## Reading -/

private def fields (j : Json) : Except String (Array (String × Json)) :=
  match j with
  | .obj m => .ok (m.toList.foldl (fun acc kv => acc.push kv) #[])
  | _ => .error "expected a JSON object"

private def field (j : Json) (k : String) : Except String Json :=
  j.getObjVal? k

private def readSigBit (j : Json) : Except String SigBit :=
  match j with
  | .num n =>
      if n.exponent == 0 && n.mantissa ≥ 0 then .ok (.net n.mantissa.toNat)
      else .error s!"signal bit is not a net id: {j.compress}"
  | .str "0" => .ok .zero
  | .str "1" => .ok .one
  | .str "x" => .ok .undef
  | .str "z" => .ok .highz
  | _ => .error s!"unrecognized signal bit {j.compress}"

private def readBits (j : Json) : Except String (Array SigBit) := do
  let a ← j.getArr?
  a.mapM readSigBit

/-- Parameters are rendered as strings: yosys writes bit strings (`INIT`)
as JSON strings and small integers as JSON numbers. -/
private def readParam (j : Json) : String :=
  match j with
  | .str s => s
  | .num n => toString n
  | _ => j.compress

private def readCell (nm : String) (j : Json) : Except String Cell := do
  let ty ← (← field j "type").getStr?
  let params ←
    match j.getObjVal? "parameters" with
    | .ok p => do
        let fs ← fields p
        pure (fs.map (fun (k, v) => (k, readParam v))).toList
    | .error _ => pure []
  let conns ←
    match j.getObjVal? "connections" with
    | .ok p => do
        let fs ← fields p
        let fs ← fs.mapM (fun (k, v) => do pure (k, ← readBits v))
        pure fs.toList
    | .error _ => pure []
  pure { name := nm, type := ty, params := params, conns := conns }

private def readModule (nm : String) (j : Json) : Except String NlModule := do
  let ports ←
    match j.getObjVal? "ports" with
    | .ok p => do
        let fs ← fields p
        let fs ← fs.mapM (fun (k, v) => do
          pure { name := k, dir := ← (← field v "direction").getStr?,
                 bits := ← readBits (← field v "bits") : Port })
        pure fs.toList
    | .error _ => pure []
  let cells ←
    match j.getObjVal? "cells" with
    | .ok p => do
        let fs ← fields p
        let fs ← fs.mapM (fun (k, v) => readCell k v)
        pure fs.toList
    | .error _ => pure []
  let nets ←
    match j.getObjVal? "netnames" with
    | .ok p => do
        let fs ← fields p
        let fs ← fs.mapM (fun (k, v) => do
          pure { name := k, bits := ← readBits (← field v "bits") : NetName })
        pure fs.toList
    | .error _ => pure []
  pure { name := nm, ports := ports, cells := cells, nets := nets }

/-- Read a whole `write_json` document into its module list. -/
def parseNetlist (text : String) : Except String (List NlModule) := do
  let j ← Json.parse text
  let ms ← field j "modules"
  let fs ← fields ms
  let out ← fs.mapM (fun (k, v) => readModule k v)
  pure out.toList

/-- Read the netlist and select the module named `top`. -/
def parseNetlistTop (text : String) (top : String) :
    Except String NlModule := do
  let ms ← parseNetlist text
  match ms.find? (fun m => m.name == top) with
  | some m => pure m
  | none =>
      .error s!"netlist has no module '{top}' (has: \
        {String.intercalate ", " (ms.map (·.name))})"

end Loom.Netlist
