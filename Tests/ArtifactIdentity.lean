-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Artifact

namespace Tests.ArtifactIdentity

example : Loom.Artifact.Identity.ofText "abc" ==
    Loom.Artifact.Identity.ofText "abc" := by decide

example : !(Loom.Artifact.Identity.ofText "abc" ==
    Loom.Artifact.Identity.ofText "abd") := by decide

example : (Loom.Artifact.Identity.ofText "abc").byteCount = 3 := by decide

#eval do
  let observation ← Loom.Artifact.observe "LICENSE" ()
  observation.verify "LICENSE"
  let mismatchNamed ← try
    observation.verify "NOTICE"
    pure false
  catch error =>
    pure ((toString error).endsWith "artifact identity mismatch: NOTICE")
  unless mismatchNamed do
    throw <| IO.userError "exact-byte observation accepted the wrong artifact"

  let license ← IO.FS.readFile "LICENSE"
  let changed ← Loom.Artifact.writeText "LICENSE" license
  if changed then
    throw <| IO.userError "deterministic writer rewrote identical bytes"
  IO.println "exact artifact observation and deterministic-write tests passed"

end Tests.ArtifactIdentity
