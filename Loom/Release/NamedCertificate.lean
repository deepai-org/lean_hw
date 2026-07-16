-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.Certificate

/-!
# Compact name-based release certificates

The generic artifact checker stores intermediate µVerilog expressions in its
proof data. Serializing those trees would destroy the sharing of a large SSA
witness. This layer stores only SSA names. Its total materializer resolves all
names through one elaboration environment and produces the existing generic
certificate, whose soundness theorem remains the sole semantic argument.
-/

namespace Loom.Release

open Loom.Emit.MicroVerilog
open Loom.Hw
open Loom.Hw.ArtifactCert

namespace Named

/-- Name-only proof data for one register-action fold. -/
inductive NextRegCert (w : Nat) where
  | same
  | write
  | seq (mid : String) (left right : NextRegCert w)
  | ite (thenCert elseCert : NextRegCert w)

/-- Name-only proof data for an ordered register-rule fold. -/
inductive NextRulesCert (w : Nat) where
  | nil
  | cons (mid : String) (head : NextRegCert w) (tail : NextRulesCert w)

structure RegCert (r : RegDecl) where
  rules : NextRulesCert r.width

inductive RegsCert : List RegDecl → Type where
  | nil : RegsCert []
  | cons {r rs} (head : RegCert r) (tail : RegsCert rs) : RegsCert (r :: rs)

/-- Three SSA names denoting one concrete write-port value. -/
structure PortNames where
  en : String
  addr : String
  data : String

/-- Name-only proof data for one memory-action fold. -/
inductive NextPortCert (aw dw : Nat) where
  | same
  | write
  | seq (mid : PortNames) (left right : NextPortCert aw dw)
  | ite (guard : String) (thenPort elsePort : PortNames)
      (thenCert elseCert : NextPortCert aw dw)

inductive NextPortRulesCert (aw dw : Nat) where
  | nil
  | cons (mid : PortNames) (head : NextPortCert aw dw)
      (tail : NextPortRulesCert aw dw)

inductive PortsCert (aw dw : Nat) : Nat → Type where
  | nil : PortsCert aw dw 0
  | cons {n} (head : NextPortRulesCert aw dw) (tail : PortsCert aw dw n) :
      PortsCert aw dw (n + 1)

structure MemCert (d : Design) (m : MemDecl) where
  ports : PortsCert m.addrWidth m.dataWidth (Compile.numPorts d m.name)

inductive MemsCert (d : Design) : List MemDecl → Type where
  | nil : MemsCert d []
  | cons {m ms} (head : MemCert d m) (tail : MemsCert d ms) :
      MemsCert d (m :: ms)

/-- Compact certificate data aligned with a source design. -/
structure ModuleCert (d : Design) where
  regs : RegsCert d.regs
  mems : MemsCert d d.mems

private def resolvePort (program : SSA.Program) (env : SSA.Env)
    (aw dw : Nat) (names : PortNames) : Option (Compile.Port aw dw) := do
  pure { en := ← program.resolve env names.en 1
         addr := ← program.resolve env names.addr aw
         data := ← program.resolve env names.data dw }

private def NextRegCert.materialize (program : SSA.Program) (env : SSA.Env) :
    {w : Nat} → NextRegCert w → Option (ArtifactCert.NextRegCert w)
  | _, .same => some .same
  | _, .write => some .write
  | w, .seq mid left right => do
      pure (.seq (← program.resolve env mid w)
        (← left.materialize program env) (← right.materialize program env))
  | _, .ite thenCert elseCert => do
      pure (.ite (← thenCert.materialize program env)
        (← elseCert.materialize program env))

private def NextRulesCert.materialize (program : SSA.Program) (env : SSA.Env) :
    {w : Nat} → NextRulesCert w → Option (ArtifactCert.NextRulesCert w)
  | _, .nil => some .nil
  | w, .cons mid head tail => do
      pure (.cons (← program.resolve env mid w)
        (← head.materialize program env) (← tail.materialize program env))

private def RegsCert.materialize (program : SSA.Program) (env : SSA.Env) :
    {regs : List RegDecl} → RegsCert regs → Option (ArtifactCert.RegsCert regs)
  | [], .nil => some .nil
  | _ :: _, .cons head tail => do
      pure (.cons ⟨← head.rules.materialize program env⟩
        (← tail.materialize program env))

private def NextPortCert.materialize (program : SSA.Program) (env : SSA.Env) :
    {aw dw : Nat} → NextPortCert aw dw → Option (ArtifactCert.NextPortCert aw dw)
  | _, _, .same => some .same
  | _, _, .write => some .write
  | aw, dw, .seq mid left right => do
      pure (.seq (← resolvePort program env aw dw mid)
        (← left.materialize program env) (← right.materialize program env))
  | aw, dw, .ite guard thenPort elsePort thenCert elseCert => do
      pure (.ite (← program.resolve env guard 1)
        (← resolvePort program env aw dw thenPort)
        (← resolvePort program env aw dw elsePort)
        (← thenCert.materialize program env)
        (← elseCert.materialize program env))

private def NextPortRulesCert.materialize (program : SSA.Program)
    (env : SSA.Env) : {aw dw : Nat} → NextPortRulesCert aw dw →
      Option (ArtifactCert.NextPortRulesCert aw dw)
  | _, _, .nil => some .nil
  | aw, dw, .cons mid head tail => do
      pure (.cons (← resolvePort program env aw dw mid)
        (← head.materialize program env) (← tail.materialize program env))

private def PortsCert.materialize (program : SSA.Program) (env : SSA.Env) :
    {aw dw n : Nat} → PortsCert aw dw n → Option (ArtifactCert.PortsCert aw dw n)
  | _, _, 0, .nil => some .nil
  | _, _, _ + 1, .cons head tail => do
      pure (.cons (← head.materialize program env)
        (← tail.materialize program env))

private def MemsCert.materialize (program : SSA.Program) (env : SSA.Env)
    (d : Design) : {mems : List MemDecl} → MemsCert d mems →
      Option (ArtifactCert.MemsCert d mems)
  | [], .nil => some .nil
  | _ :: _, .cons head tail => do
      pure (.cons ⟨← head.ports.materialize program env⟩
        (← tail.materialize program env d))

/-- Resolve a compact name certificate to the already-proved generic
certificate type. Failure is explicit and makes the release checker reject. -/
def ModuleCert.materialize (program : SSA.Program) (env : SSA.Env)
    {d : Design} (cert : ModuleCert d) : Option (ArtifactCert.ModuleCert d) := do
  pure { regs := ← cert.regs.materialize program env
         mems := ← cert.mems.materialize program env d }

end Named

/-- Validate a compact name-only certificate against an arbitrary program. -/
def ssaNamedMatches (design : Design) (program : SSA.Program)
    (cert : Named.ModuleCert design) : Bool :=
  match program.elaborateEnv with
  | none => false
  | some env =>
      match program.elaborateWithEnv env, cert.materialize program env with
      | some module, some materialized =>
          ArtifactCert.moduleMatches design module materialized
      | _, _ => false

/-- Compact certificates remain untrusted proof data: acceptance alone yields
transition-system equality with the reference compiler. -/
theorem ssaNamedMatches_behavior (design : Design) (program : SSA.Program)
    (cert : Named.ModuleCert design)
    (h : ssaNamedMatches design program cert = true) :
    ∃ module, program.elaborate = some module ∧
      module.toTSys = (Compile.compile design).toTSys := by
  unfold ssaNamedMatches at h
  split at h <;> try contradiction
  rename_i env henv
  split at h <;> try contradiction
  rename_i module materialized hmodule hmaterialized
  refine ⟨module, ?_, ?_⟩
  · unfold SSA.Program.elaborate
    simp [henv, hmodule]
  · exact (ArtifactCert.moduleMatches_sound design module materialized h).toTSys_eq

end Loom.Release
