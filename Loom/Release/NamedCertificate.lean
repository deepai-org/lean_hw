-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.Certificate
import Loom.Release.KernelDecide

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
  | seq (mid : Option String) (left right : NextRegCert w)
  | ite (thenCert elseCert : NextRegCert w)

/-- Name-only proof data for an ordered register-rule fold. -/
inductive NextRulesCert (w : Nat) where
  | nil
  | cons (mid : Option String) (head : NextRegCert w) (tail : NextRulesCert w)

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
  | seq (mid : Option PortNames) (left right : NextPortCert aw dw)
  | ite (guard : String) (thenPort elsePort : PortNames)
      (thenCert elseCert : NextPortCert aw dw)

inductive NextPortRulesCert (aw dw : Nat) where
  | nil
  | cons (mid : Option PortNames) (head : NextPortCert aw dw)
      (tail : NextPortRulesCert aw dw)

inductive PortsCert (aw dw : Nat) : Nat → Type where
  | nil : PortsCert aw dw 0
  | cons {n} (head : NextPortRulesCert aw dw) (tail : PortsCert aw dw n) :
      PortsCert aw dw (n + 1)

structure MemCert (d : Design) (m : MemDecl) where
  numPorts : Nat
  ports : PortsCert m.addrWidth m.dataWidth numPorts

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

private def resolveExprRef {w : Nat} (program : SSA.Program) (env : SSA.Env)
    (fallback : Loom.Emit.MicroVerilog.Expr w) : Option String →
      Option (Loom.Emit.MicroVerilog.Expr w)
  | some name => program.resolve env name w
  | none => some fallback

private def NextRegCert.materialize (program : SSA.Program) (env : SSA.Env)
    (rn : String) : {w : Nat} → (action : Act) →
      Loom.Emit.MicroVerilog.Expr w → NextRegCert w →
      Option (ArtifactCert.NextRegCert w)
  | _, _, _, .same => some .same
  | _, _, _, .write => some .write
  | w, .seq leftAction rightAction, cur, .seq mid left right => do
      let computed := Compile.nextReg rn w leftAction cur
      let mid ← resolveExprRef program env computed mid
      pure (.seq mid
        (← left.materialize program env rn leftAction cur)
        (← right.materialize program env rn rightAction mid))
  | _, .ite _ thenAction elseAction, cur, .ite thenCert elseCert => do
      pure (.ite (← thenCert.materialize program env rn thenAction cur)
        (← elseCert.materialize program env rn elseAction cur))
  | _, _, _, _ => none

private def NextRulesCert.materialize (program : SSA.Program) (env : SSA.Env)
    (rn : String) : {w : Nat} → (rules : List Rule) →
      Loom.Emit.MicroVerilog.Expr w → NextRulesCert w →
      Option (ArtifactCert.NextRulesCert w)
  | _, [], _, .nil => some .nil
  | w, rule :: rules, cur, .cons mid head tail => do
      let computed := Compile.nextReg rn w rule.body cur
      let mid ← resolveExprRef program env computed mid
      pure (.cons mid
        (← head.materialize program env rn rule.body cur)
        (← tail.materialize program env rn rules mid))
  | _, _, _, _ => none

private def RegsCert.materialize (program : SSA.Program) (env : SSA.Env)
    (rules : List Rule) : {regs : List RegDecl} → RegsCert regs →
      Option (ArtifactCert.RegsCert regs)
  | [], .nil => some .nil
  | reg :: _, .cons head tail => do
      pure (.cons ⟨← head.rules.materialize program env reg.name rules
        (.reg reg.width reg.name)⟩
        (← tail.materialize program env rules))

private def resolvePortRef {aw dw : Nat} (program : SSA.Program) (env : SSA.Env)
    (fallback : Compile.Port aw dw) : Option PortNames →
      Option (Compile.Port aw dw)
  | some names => resolvePort program env aw dw names
  | none => some fallback

private def NextPortCert.materialize (program : SSA.Program) (env : SSA.Env)
    (mn : String) (p : Nat) : {aw dw : Nat} → (action : Act) →
      Compile.Port aw dw → NextPortCert aw dw →
      Option (ArtifactCert.NextPortCert aw dw)
  | _, _, _, _, .same => some .same
  | _, _, _, _, .write => some .write
  | aw, dw, .seq leftAction rightAction, cur, .seq mid left right => do
      let computed := Compile.memPort mn aw dw p leftAction cur
      let mid ← resolvePortRef program env computed mid
      pure (.seq mid
        (← left.materialize program env mn p leftAction cur)
        (← right.materialize program env mn p rightAction mid))
  | aw, dw, .ite _ thenAction elseAction, cur,
      .ite guard thenPort elsePort thenCert elseCert => do
      pure (.ite (← program.resolve env guard 1)
        (← resolvePort program env aw dw thenPort)
        (← resolvePort program env aw dw elsePort)
        (← thenCert.materialize program env mn p thenAction cur)
        (← elseCert.materialize program env mn p elseAction cur))
  | _, _, _, _, _ => none

private def NextPortRulesCert.materialize (program : SSA.Program)
    (env : SSA.Env) (mn : String) (p : Nat) : {aw dw : Nat} →
      (rules : List Rule) → Compile.Port aw dw → NextPortRulesCert aw dw →
      Option (ArtifactCert.NextPortRulesCert aw dw)
  | _, _, [], _, .nil => some .nil
  | aw, dw, rule :: rules, cur, .cons mid head tail => do
      let computed := Compile.memPort mn aw dw p rule.body cur
      let mid ← resolvePortRef program env computed mid
      pure (.cons mid
        (← head.materialize program env mn p rule.body cur)
        (← tail.materialize program env mn p rules mid))
  | _, _, _, _, _ => none

private def PortsCert.materialize (program : SSA.Program) (env : SSA.Env)
    (mn : String) (rules : List Rule) : {aw dw n : Nat} →
      (p : Nat) → PortsCert aw dw n → Option (ArtifactCert.PortsCert aw dw n)
  | _, _, 0, _, .nil => some .nil
  | aw, dw, _ + 1, p, .cons head tail => do
      let start : Compile.Port aw dw :=
        { en := .lit 0, addr := .lit 0, data := .lit 0 }
      pure (.cons (← head.materialize program env mn p rules start)
        (← tail.materialize program env mn rules (p + 1)))

private def MemsCert.materialize (program : SSA.Program) (env : SSA.Env)
    (d : Design) : {mems : List MemDecl} → MemsCert d mems →
      Option (ArtifactCert.MemsCert d mems)
  | [], .nil => some .nil
  | m :: _, .cons head tail =>
    if h : head.numPorts = Compile.numPorts d m.name then do
      let ports : PortsCert m.addrWidth m.dataWidth
          (Compile.numPorts d m.name) :=
        Eq.mp (congrArg (PortsCert m.addrWidth m.dataWidth) h) head.ports
      pure (.cons ⟨← ports.materialize program env m.name d.rules 0⟩
        (← tail.materialize program env d))
    else none

/-- Resolve a compact name certificate to the already-proved generic
certificate type. Failure is explicit and makes the release checker reject. -/
def ModuleCert.materialize (program : SSA.Program) (env : SSA.Env)
    {d : Design} (cert : ModuleCert d) : Option (ArtifactCert.ModuleCert d) := do
  pure { regs := ← cert.regs.materialize program env d.rules
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

/-- Publication-facing parser-free boundary using compact name-only proof
data: exact rendered bytes and exact compiled transition-system behavior. -/
theorem exactRenderingAndNamedCompilation (design : Design)
    (program : SSA.Program) (disk : Rope (List String))
    (cert : Named.ModuleCert design)
    (renderedLines : Rope (List String))
    (hrender : renderedLines = program.renderTree)
    (hdisk : renderedLines = disk)
    (hcert : ssaNamedMatches design program cert = true) :
    program.renderTree.flattenUTF8 = disk.flattenUTF8 ∧
    ∃ module, program.elaborate = some module ∧
      module.toTSys = (Compile.compile design).toTSys := by
  exact ⟨Rope.flattenUTF8_congr (hrender.symm.trans hdisk),
    ssaNamedMatches_behavior design program cert hcert⟩

end Loom.Release
