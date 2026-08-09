-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64mini.DebugMap

/-! Lightweight generator for the board-only LNP64mini debug include. It does
not import or construct the machine; the separate `DebugMapCheck` module owns
the build-time composed-design certificate. -/

def main (args : List String) : IO Unit :=
  match args with
  | [] => Machines.Lnp64mini.DebugMap.emit
  | ["--check"] => Machines.Lnp64mini.DebugMap.check
  | _ => throw <| IO.userError "usage: lake exe debugmap [--check]"
