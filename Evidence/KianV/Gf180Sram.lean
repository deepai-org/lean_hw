-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ExternalComponent

/-! # KianV GF180 512x8 SRAM external-component contract

The technology macro remains outside Loom logic. This contract states the
behavior used by KianV's wrapper; `gf180_sram_external.json` binds the physical
views and wrapper to exact hashes. Supplying bytes constructs an exact
`ExternalBinding`, but does not turn the named external evidence premise into
a kernel theorem.
-/

namespace Evidence.KianV.Gf180Sram

open Loom.Hw

private def port (name : String) (direction : PortDirection) (width : Nat)
    (semanticType : String := "bits") : PortDecl :=
  { name, direction, width, semanticType, domain := "sram" }

private def clk := port "CLK" .input 1 "clock"
private def cen := port "CEN" .input 1
private def gwen := port "GWEN" .input 1
private def wen := port "WEN" .input 8
private def address := port "A" .input 9
private def data := port "D" .input 8
private def q := port "Q" .output 8

def interface : ComponentInterface :=
  ⟨[clk, cen, gwen, wen, address, data, q]⟩

structure State where
  memory : Nat → BitVec 8
  output : BitVec 8

private def maskedWord (old next writeEnableN : BitVec 8) : BitVec 8 :=
  (old &&& writeEnableN) ||| (next &&& ~~~writeEnableN)

private def transition (event : ComponentEvent) (input : PortEnv)
    (before after : State) : Prop :=
  if !event.ticks "sram" then after = before
  else if input "CEN" 1 = 0 then
    after.output = before.memory (input "A" 9).toNat ∧
      after.memory = if input "GWEN" 1 = 0 then
        Function.update before.memory (input "A" 9).toNat
          (maskedWord (before.memory (input "A" 9).toNat)
            (input "D" 8) (input "WEN" 8))
      else before.memory
  else
    -- The macro's disabled-cycle Q is deliberately not constrained; memory
    -- must hold. The simulation wrapper represents this Q freedom with X.
    after.memory = before.memory

def behavior : ComponentContract interface where
  State := State
  init := fun _ => True
  step := transition
  observe := fun _ state name width =>
    if name = "Q" then state.output.setWidth width else 0
  step_input_congr := by
    intro event before after left right agree
    have hCen : left "CEN" 1 = right "CEN" 1 := by
      simpa [cen, port] using agree cen (by native_decide)
    have hGwen : left "GWEN" 1 = right "GWEN" 1 := by
      simpa [gwen, port] using agree gwen (by native_decide)
    have hWen : left "WEN" 8 = right "WEN" 8 := by
      simpa [wen, port] using agree wen (by native_decide)
    have hAddress : left "A" 9 = right "A" 9 := by
      simpa [address, port] using agree address (by native_decide)
    have hData : left "D" 8 = right "D" 8 := by
      simpa [data, port] using agree data (by native_decide)
    simp only [transition]
    rw [hCen, hGwen, hWen, hAddress, hData]
  observe_input_congr := by
    intro state left right agree outputPort member
    rfl

def specification : ExternalComponent where
  name := "gf180mcu_fd_ip_sram__sram512x8m8wm1"
  version := "kianv-wrapper-517bd60a435e-pdk-fb4b8f59451d"
  interface := interface
  behavior := behavior
  domains := [⟨"sram", .rising, .resetless⟩]
  combinational := []
  latency := [⟨"Q", some "A", 1, some 1⟩]

theorem specification_valid : specification.validB = true := by native_decide

/-- Bind exact wrapper bytes after the physical-view manifest verifier has
checked the wrapper/GDS/LEF/blackbox/Liberty SHA-256 inventory. -/
def bindWrapper (bytes : ByteArray) : ExternalBinding specification where
  format := .verilog
  moduleName := "gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper"
  parameters := []
  artifact := ⟨bytes⟩
  evidence := .assumptionOnly
  assumptions := [
    ⟨"macro_contract",
      "the hash-bound GF180 wrapper and macro views implement the 512x8 active-low masked synchronous-read contract"⟩]

theorem binding_valid (bytes : ByteArray) : (bindWrapper bytes).validB = true := by
  simp [bindWrapper, ExternalBinding.validB, specification_valid]
  native_decide

end Evidence.KianV.Gf180Sram
