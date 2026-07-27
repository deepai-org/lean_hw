-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.SymbolicCertificate

/-! Stable bounded join certificates for action-wide release checking. -/

namespace Loom.Release.Symbolic.ActionWide

open Loom.Release.SSA

/-- One concrete mux used to join a register changed by an `ite`. -/
structure Join where
  index : Nat
  width : Nat
  guard : Ref
  thenInput : Ref
  elseInput : Ref
  output : Ref
  deriving Repr, DecidableEq

private def localJoinMatches (base : Nat) (block : List IndexedWire)
    (join : Join) : Bool :=
  let check (number : Nat) :=
      if number < base then false else
      match block[number - base]? with
      | some ⟨actualNumber, actualWidth,
          .mux actualGuard actualThen actualElse⟩ =>
          actualNumber == number && actualWidth == join.width &&
            join.guard == actualGuard && join.thenInput == actualThen &&
            join.elseInput == actualElse
      | _ => false
  match join.output with
  | .wire number => check number
  | .namedWire number _ => check number
  | .reg _ => false

/-- Check joins against one bounded indexed-wire leaf. -/
def localJoinBlockMatches (base : Nat) (block : List IndexedWire)
    (joins : List Join) : Bool :=
  joins.all (localJoinMatches base block)

end Loom.Release.Symbolic.ActionWide
