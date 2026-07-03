import Loom.Hw.Compile
import Loom.Emit.MicroVerilog.Print

/-!
# Multi-write-port regression (wrPorts)

A miniature of the LNP64-µ Mover-phase shape: one memory written up to
three times in one cycle — a "core" store on port 0, a "mover" data word on
port 1, and a "mover" status word on port 2 — with priority = port order
(later port wins on an address collision, matching the EDSL's
last-write-wins rule order).

Checks, at elaboration time (`#guard`, kernel-evaluated):
* the EDSL cycle and the compiled µVerilog module cycle agree at every
  address, including a three-way collision;
* the compiler derives the port count from the used indices;
* `MemWriteWF` holds for the design (`decide`), so `compile_cycle_mems`
  applies — instantiated below as a theorem with no extra reasoning.
-/

namespace Tests.MultiPort

open Loom.Hw Loom.Hw.Compile

/-- Three same-cycle writes to `m`: port 0 at `a0`, ports 1 and 2 at `a1`
(ports 1/2 always collide; setting `a0 = a1` collides all three). -/
private def design (a0 a1 : BitVec 4) (en0 : Bool) : Design where
  name := "multiport"
  regs := [⟨"a0", 4, a0⟩, ⟨"a1", 4, a1⟩, ⟨"c0", 1, if en0 then 1 else 0⟩]
  mems := [{ name := "m", addrWidth := 4, dataWidth := 8, init := fun _ => 0 }]
  rules :=
    [ ⟨"core", .ite (.reg 1 "c0")
        (.memWrite 4 8 "m" 0 (.reg 4 "a0") (.lit 11)) .skip⟩
    , ⟨"mover", .seq
        (.memWrite 4 8 "m" 1 (.reg 4 "a1") (.lit 22))
        (.memWrite 4 8 "m" 2 (.reg 4 "a1") (.lit 33))⟩ ]

private def mDecl : MemDecl :=
  { name := "m", addrWidth := 4, dataWidth := 8, init := fun _ => 0 }

/-- EDSL and compiled module agree on the memory at every address. -/
private def agree (a0 a1 : BitVec 4) (en0 : Bool) : Bool :=
  let d := design a0 a1 en0
  let hw := d.cycle d.reset
  let mv := (Loom.Emit.MicroVerilog.Module.cycle (compile d) (convSt d.reset))
  (List.range 16).all fun a => hw.mems "m" a 8 == mv.mems "m" a 8

-- distinct addresses: port 0 lands at 4, port 2 wins over port 1 at 7
#guard agree 4 7 true
#guard (((design 4 7 true).cycle (design 4 7 true).reset).mems "m" 4 8) == 11
#guard (((design 4 7 true).cycle (design 4 7 true).reset).mems "m" 7 8) == 33
-- three-way collision: the highest port (last write in rule order) wins
#guard agree 5 5 true
#guard (((design 5 5 true).cycle (design 5 5 true).reset).mems "m" 5 8) == 33
-- core write disabled: the mover ports still commit
#guard agree 9 2 false
#guard (((design 9 2 false).cycle (design 9 2 false).reset).mems "m" 9 8) == 0
#guard (((design 9 2 false).cycle (design 9 2 false).reset).mems "m" 2 8) == 33
-- the compiler derived three write ports
#guard ((compile (design 0 1 true)).mems.map (·.wrPorts.length)) == [3]

/-- The design satisfies the memory-half correctness precondition. -/
private theorem wf (a0 a1 : BitVec 4) (en0 : Bool) :
    MemWriteWF (design a0 a1 en0) mDecl := by
  constructor
  · intro rl hrl
    rcases List.mem_cons.mp hrl with rfl | hrl
    · rfl
    rcases List.mem_cons.mp hrl with rfl | hrl
    · rfl
    · cases hrl
  · rw [show designTrace (design a0 a1 en0) mDecl.name = [0, 1, 2] from rfl]
    refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · cases hb
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · cases hb
    · intro b hb; cases hb

/-- `compile_cycle_mems` instantiated: the emitted module's memory equals
the design's, every cycle, at every address. -/
private theorem multiport_mems_correct (a0 a1 : BitVec 4) (en0 : Bool)
    (σ : Loom.Hw.St) (x : Nat) :
    (Loom.Emit.MicroVerilog.Module.cycle (compile (design a0 a1 en0))
        (convSt σ)).mems "m" x 8
      = ((design a0 a1 en0).cycle σ).mems "m" x 8 :=
  compile_cycle_mems (design a0 a1 en0) σ mDecl
    (by rw [show (design a0 a1 en0).mems = [mDecl] from rfl]; exact List.mem_cons_self ..)
    (by rw [show (design a0 a1 en0).mems.map (·.name) = ["m"] from rfl]
        exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩)
    (wf a0 a1 en0) x

#eval do
  let d := design 5 5 true
  IO.println s!"multiport: numPorts = {numPorts d "m"}, collision value = {((d.cycle d.reset).mems "m" 5 8).toNat}"

end Tests.MultiPort
