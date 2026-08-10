-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0

/-!
# Generic artifact identity and deterministic writing

External evidence must identify the bytes it observed. `Identity` deliberately
keeps the exact bytes: it has no collision assumption and can be converted to
a compact digest by an integration layer such as `scripts/artifact_identity.py`.
-/

namespace Loom.Artifact

/-- Collision-free identity inside Loom: equality means byte equality. -/
structure Identity where
  bytes : ByteArray
  deriving BEq

def Identity.ofText (text : String) : Identity := ⟨text.toUTF8⟩

def Identity.byteCount (identity : Identity) : Nat := identity.bytes.size

def identify (path : System.FilePath) : IO Identity :=
  return ⟨← IO.FS.readBinFile path⟩

/-- A value observed from one exact external artifact. Board transports and
health policy remain outside this generic provenance envelope. -/
structure Observation (Value : Type) where
  artifact : Identity
  value    : Value

def observe {Value : Type} (path : System.FilePath) (value : Value) :
    IO (Observation Value) :=
  return { artifact := ← identify path, value }

/-- Refuse to apply an observation to bytes other than those that produced it. -/
def Observation.verify {Value : Type} (observation : Observation Value)
    (path : System.FilePath) : IO Unit := do
  let current ← identify path
  if current != observation.artifact then
    throw <| IO.userError s!"artifact identity mismatch: {path}"

/-- Write text only when its exact bytes differ. Repeating an emission with
the same value preserves the artifact's timestamp, making freshness checks
meaningful rather than self-invalidating. -/
def writeText (path : System.FilePath) (text : String) : IO Bool := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  if ← path.pathExists then
    if (← IO.FS.readBinFile path) == text.toUTF8 then return false
  IO.FS.writeFile path text
  return true

end Loom.Artifact
