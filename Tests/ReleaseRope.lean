-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.Rope

namespace Tests.ReleaseRope

open Loom.Release

private def witness : Rope Nat :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3))

private def render (n : Nat) : List String := [toString n]

private def artifact : Rendered Nat where
  witness := witness
  disk := .node (.leaf ["1"]) (.node (.leaf ["2"]) (.leaf ["3"]))

private theorem left : (Rope.leaf 1).map render = .leaf ["1"] := rfl
private theorem middle : (Rope.leaf 2).map render = .leaf ["2"] := rfl
private theorem right : (Rope.leaf 3).map render = .leaf ["3"] := rfl

private theorem root : artifact.renderTree render = artifact.disk := by
  exact Rope.node_congr left (Rope.node_congr middle right)

example : (artifact.renderTree render).flattenBytes =
    artifact.disk.flattenBytes := Rope.flattenBytes_congr root

example : (artifact.renderTree render).flattenUTF8 =
    artifact.disk.flattenUTF8 := artifact.exactBytes render root

example : artifact.disk.flattenBytes = "1\n2\n3" := by decide +kernel

end Tests.ReleaseRope
