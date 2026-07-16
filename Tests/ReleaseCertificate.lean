-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.Certificate

/-! Type-level regression for the parser-free release theorem. Concrete
module certificates are exercised in `Tests.ArtifactCert`; this file pins the
exact rendered-byte half without introducing a fake generator assumption. -/

namespace Tests.ReleaseCertificate

open Loom.Release
open Loom.Release.SSA

private def program : Program where
  name := "empty"
  regs := []
  mems := []
  wires := []
  outs := []

private def disk : Rope (List String) :=
  .node (.leaf ["module empty(", "  input wire clk,"])
    (.leaf ["  input wire rst", ");", "  always @(posedge clk) begin",
      "    if (rst) begin", "    end else begin", "    end", "  end",
      "endmodule"])

private def rendered : Rope (List String) := disk

example : rendered.flattenLists = program.render := by decide +kernel

example : String.intercalate "\n" program.render = disk.flattenBytes := by
  unfold Rope.flattenBytes
  rw [← show rendered.flattenLists = program.render by decide +kernel]
  rfl

end Tests.ReleaseCertificate
