-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCResetCanon

/-!
# R-MC support: domain reset lookup arms

Generated reset lookup families for `RMC.absDom_reset`, using the optimized
literal declaration list from `RMCResetDeclList.lean`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom.Hw Machines.Lnp64u.Hw


set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dreg (m : Manifest) : ∀ (d : DomainId) (r : RegId),
    (Hw.core m).reset.regs (Hw.dreg d r) 32
      = (m.initState.doms d).regs r
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 0 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 1 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 2 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 3 (by omega)
  | ⟨0, _⟩, ⟨4, _⟩ => reset_lookup_decl m 4 (by omega)
  | ⟨0, _⟩, ⟨5, _⟩ => reset_lookup_decl m 5 (by omega)
  | ⟨0, _⟩, ⟨6, _⟩ => reset_lookup_decl m 6 (by omega)
  | ⟨0, _⟩, ⟨7, _⟩ => reset_lookup_decl m 7 (by omega)
  | ⟨0, _⟩, ⟨n+8, h⟩ => by simp [numRegs] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 137 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 138 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 139 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 140 (by omega)
  | ⟨1, _⟩, ⟨4, _⟩ => reset_lookup_decl m 141 (by omega)
  | ⟨1, _⟩, ⟨5, _⟩ => reset_lookup_decl m 142 (by omega)
  | ⟨1, _⟩, ⟨6, _⟩ => reset_lookup_decl m 143 (by omega)
  | ⟨1, _⟩, ⟨7, _⟩ => reset_lookup_decl m 144 (by omega)
  | ⟨1, _⟩, ⟨n+8, h⟩ => by simp [numRegs] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 274 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 275 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 276 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 277 (by omega)
  | ⟨2, _⟩, ⟨4, _⟩ => reset_lookup_decl m 278 (by omega)
  | ⟨2, _⟩, ⟨5, _⟩ => reset_lookup_decl m 279 (by omega)
  | ⟨2, _⟩, ⟨6, _⟩ => reset_lookup_decl m 280 (by omega)
  | ⟨2, _⟩, ⟨7, _⟩ => reset_lookup_decl m 281 (by omega)
  | ⟨2, _⟩, ⟨n+8, h⟩ => by simp [numRegs] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 411 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 412 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 413 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 414 (by omega)
  | ⟨3, _⟩, ⟨4, _⟩ => reset_lookup_decl m 415 (by omega)
  | ⟨3, _⟩, ⟨5, _⟩ => reset_lookup_decl m 416 (by omega)
  | ⟨3, _⟩, ⟨6, _⟩ => reset_lookup_decl m 417 (by omega)
  | ⟨3, _⟩, ⟨7, _⟩ => reset_lookup_decl m 418 (by omega)
  | ⟨3, _⟩, ⟨n+8, h⟩ => by simp [numRegs] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dpc (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.dpc d) 12
      = (m.initState.doms d).pc
  | ⟨0, _⟩ => reset_lookup_decl m 8 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 145 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 282 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 419 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dcapLinV (m : Manifest) : ∀ (d : DomainId) (s : Slot),
    (Hw.core m).reset.regs (Hw.dcapLinV d s) 1
      = (if (((m.initState.doms d).caps s).bind (·.lineage)).isSome then 1 else 0)
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 11 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 16 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 21 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 26 (by omega)
  | ⟨0, _⟩, ⟨4, _⟩ => reset_lookup_decl m 31 (by omega)
  | ⟨0, _⟩, ⟨5, _⟩ => reset_lookup_decl m 36 (by omega)
  | ⟨0, _⟩, ⟨6, _⟩ => reset_lookup_decl m 41 (by omega)
  | ⟨0, _⟩, ⟨7, _⟩ => reset_lookup_decl m 46 (by omega)
  | ⟨0, _⟩, ⟨8, _⟩ => reset_lookup_decl m 51 (by omega)
  | ⟨0, _⟩, ⟨9, _⟩ => reset_lookup_decl m 56 (by omega)
  | ⟨0, _⟩, ⟨10, _⟩ => reset_lookup_decl m 61 (by omega)
  | ⟨0, _⟩, ⟨11, _⟩ => reset_lookup_decl m 66 (by omega)
  | ⟨0, _⟩, ⟨12, _⟩ => reset_lookup_decl m 71 (by omega)
  | ⟨0, _⟩, ⟨13, _⟩ => reset_lookup_decl m 76 (by omega)
  | ⟨0, _⟩, ⟨14, _⟩ => reset_lookup_decl m 81 (by omega)
  | ⟨0, _⟩, ⟨15, _⟩ => reset_lookup_decl m 86 (by omega)
  | ⟨0, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 148 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 153 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 158 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 163 (by omega)
  | ⟨1, _⟩, ⟨4, _⟩ => reset_lookup_decl m 168 (by omega)
  | ⟨1, _⟩, ⟨5, _⟩ => reset_lookup_decl m 173 (by omega)
  | ⟨1, _⟩, ⟨6, _⟩ => reset_lookup_decl m 178 (by omega)
  | ⟨1, _⟩, ⟨7, _⟩ => reset_lookup_decl m 183 (by omega)
  | ⟨1, _⟩, ⟨8, _⟩ => reset_lookup_decl m 188 (by omega)
  | ⟨1, _⟩, ⟨9, _⟩ => reset_lookup_decl m 193 (by omega)
  | ⟨1, _⟩, ⟨10, _⟩ => reset_lookup_decl m 198 (by omega)
  | ⟨1, _⟩, ⟨11, _⟩ => reset_lookup_decl m 203 (by omega)
  | ⟨1, _⟩, ⟨12, _⟩ => reset_lookup_decl m 208 (by omega)
  | ⟨1, _⟩, ⟨13, _⟩ => reset_lookup_decl m 213 (by omega)
  | ⟨1, _⟩, ⟨14, _⟩ => reset_lookup_decl m 218 (by omega)
  | ⟨1, _⟩, ⟨15, _⟩ => reset_lookup_decl m 223 (by omega)
  | ⟨1, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 285 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 290 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 295 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 300 (by omega)
  | ⟨2, _⟩, ⟨4, _⟩ => reset_lookup_decl m 305 (by omega)
  | ⟨2, _⟩, ⟨5, _⟩ => reset_lookup_decl m 310 (by omega)
  | ⟨2, _⟩, ⟨6, _⟩ => reset_lookup_decl m 315 (by omega)
  | ⟨2, _⟩, ⟨7, _⟩ => reset_lookup_decl m 320 (by omega)
  | ⟨2, _⟩, ⟨8, _⟩ => reset_lookup_decl m 325 (by omega)
  | ⟨2, _⟩, ⟨9, _⟩ => reset_lookup_decl m 330 (by omega)
  | ⟨2, _⟩, ⟨10, _⟩ => reset_lookup_decl m 335 (by omega)
  | ⟨2, _⟩, ⟨11, _⟩ => reset_lookup_decl m 340 (by omega)
  | ⟨2, _⟩, ⟨12, _⟩ => reset_lookup_decl m 345 (by omega)
  | ⟨2, _⟩, ⟨13, _⟩ => reset_lookup_decl m 350 (by omega)
  | ⟨2, _⟩, ⟨14, _⟩ => reset_lookup_decl m 355 (by omega)
  | ⟨2, _⟩, ⟨15, _⟩ => reset_lookup_decl m 360 (by omega)
  | ⟨2, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 422 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 427 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 432 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 437 (by omega)
  | ⟨3, _⟩, ⟨4, _⟩ => reset_lookup_decl m 442 (by omega)
  | ⟨3, _⟩, ⟨5, _⟩ => reset_lookup_decl m 447 (by omega)
  | ⟨3, _⟩, ⟨6, _⟩ => reset_lookup_decl m 452 (by omega)
  | ⟨3, _⟩, ⟨7, _⟩ => reset_lookup_decl m 457 (by omega)
  | ⟨3, _⟩, ⟨8, _⟩ => reset_lookup_decl m 462 (by omega)
  | ⟨3, _⟩, ⟨9, _⟩ => reset_lookup_decl m 467 (by omega)
  | ⟨3, _⟩, ⟨10, _⟩ => reset_lookup_decl m 472 (by omega)
  | ⟨3, _⟩, ⟨11, _⟩ => reset_lookup_decl m 477 (by omega)
  | ⟨3, _⟩, ⟨12, _⟩ => reset_lookup_decl m 482 (by omega)
  | ⟨3, _⟩, ⟨13, _⟩ => reset_lookup_decl m 487 (by omega)
  | ⟨3, _⟩, ⟨14, _⟩ => reset_lookup_decl m 492 (by omega)
  | ⟨3, _⟩, ⟨15, _⟩ => reset_lookup_decl m 497 (by omega)
  | ⟨3, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dcapLin (m : Manifest) : ∀ (d : DomainId) (s : Slot),
    (Hw.core m).reset.regs (Hw.dcapLin d s) 4
      = (((((m.initState.doms d).caps s).bind (·.lineage)).map fun l => BitVec.ofNat 4 l.val).getD 0)
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 12 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 17 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 22 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 27 (by omega)
  | ⟨0, _⟩, ⟨4, _⟩ => reset_lookup_decl m 32 (by omega)
  | ⟨0, _⟩, ⟨5, _⟩ => reset_lookup_decl m 37 (by omega)
  | ⟨0, _⟩, ⟨6, _⟩ => reset_lookup_decl m 42 (by omega)
  | ⟨0, _⟩, ⟨7, _⟩ => reset_lookup_decl m 47 (by omega)
  | ⟨0, _⟩, ⟨8, _⟩ => reset_lookup_decl m 52 (by omega)
  | ⟨0, _⟩, ⟨9, _⟩ => reset_lookup_decl m 57 (by omega)
  | ⟨0, _⟩, ⟨10, _⟩ => reset_lookup_decl m 62 (by omega)
  | ⟨0, _⟩, ⟨11, _⟩ => reset_lookup_decl m 67 (by omega)
  | ⟨0, _⟩, ⟨12, _⟩ => reset_lookup_decl m 72 (by omega)
  | ⟨0, _⟩, ⟨13, _⟩ => reset_lookup_decl m 77 (by omega)
  | ⟨0, _⟩, ⟨14, _⟩ => reset_lookup_decl m 82 (by omega)
  | ⟨0, _⟩, ⟨15, _⟩ => reset_lookup_decl m 87 (by omega)
  | ⟨0, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 149 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 154 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 159 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 164 (by omega)
  | ⟨1, _⟩, ⟨4, _⟩ => reset_lookup_decl m 169 (by omega)
  | ⟨1, _⟩, ⟨5, _⟩ => reset_lookup_decl m 174 (by omega)
  | ⟨1, _⟩, ⟨6, _⟩ => reset_lookup_decl m 179 (by omega)
  | ⟨1, _⟩, ⟨7, _⟩ => reset_lookup_decl m 184 (by omega)
  | ⟨1, _⟩, ⟨8, _⟩ => reset_lookup_decl m 189 (by omega)
  | ⟨1, _⟩, ⟨9, _⟩ => reset_lookup_decl m 194 (by omega)
  | ⟨1, _⟩, ⟨10, _⟩ => reset_lookup_decl m 199 (by omega)
  | ⟨1, _⟩, ⟨11, _⟩ => reset_lookup_decl m 204 (by omega)
  | ⟨1, _⟩, ⟨12, _⟩ => reset_lookup_decl m 209 (by omega)
  | ⟨1, _⟩, ⟨13, _⟩ => reset_lookup_decl m 214 (by omega)
  | ⟨1, _⟩, ⟨14, _⟩ => reset_lookup_decl m 219 (by omega)
  | ⟨1, _⟩, ⟨15, _⟩ => reset_lookup_decl m 224 (by omega)
  | ⟨1, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 286 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 291 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 296 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 301 (by omega)
  | ⟨2, _⟩, ⟨4, _⟩ => reset_lookup_decl m 306 (by omega)
  | ⟨2, _⟩, ⟨5, _⟩ => reset_lookup_decl m 311 (by omega)
  | ⟨2, _⟩, ⟨6, _⟩ => reset_lookup_decl m 316 (by omega)
  | ⟨2, _⟩, ⟨7, _⟩ => reset_lookup_decl m 321 (by omega)
  | ⟨2, _⟩, ⟨8, _⟩ => reset_lookup_decl m 326 (by omega)
  | ⟨2, _⟩, ⟨9, _⟩ => reset_lookup_decl m 331 (by omega)
  | ⟨2, _⟩, ⟨10, _⟩ => reset_lookup_decl m 336 (by omega)
  | ⟨2, _⟩, ⟨11, _⟩ => reset_lookup_decl m 341 (by omega)
  | ⟨2, _⟩, ⟨12, _⟩ => reset_lookup_decl m 346 (by omega)
  | ⟨2, _⟩, ⟨13, _⟩ => reset_lookup_decl m 351 (by omega)
  | ⟨2, _⟩, ⟨14, _⟩ => reset_lookup_decl m 356 (by omega)
  | ⟨2, _⟩, ⟨15, _⟩ => reset_lookup_decl m 361 (by omega)
  | ⟨2, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 423 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 428 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 433 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 438 (by omega)
  | ⟨3, _⟩, ⟨4, _⟩ => reset_lookup_decl m 443 (by omega)
  | ⟨3, _⟩, ⟨5, _⟩ => reset_lookup_decl m 448 (by omega)
  | ⟨3, _⟩, ⟨6, _⟩ => reset_lookup_decl m 453 (by omega)
  | ⟨3, _⟩, ⟨7, _⟩ => reset_lookup_decl m 458 (by omega)
  | ⟨3, _⟩, ⟨8, _⟩ => reset_lookup_decl m 463 (by omega)
  | ⟨3, _⟩, ⟨9, _⟩ => reset_lookup_decl m 468 (by omega)
  | ⟨3, _⟩, ⟨10, _⟩ => reset_lookup_decl m 473 (by omega)
  | ⟨3, _⟩, ⟨11, _⟩ => reset_lookup_decl m 478 (by omega)
  | ⟨3, _⟩, ⟨12, _⟩ => reset_lookup_decl m 483 (by omega)
  | ⟨3, _⟩, ⟨13, _⟩ => reset_lookup_decl m 488 (by omega)
  | ⟨3, _⟩, ⟨14, _⟩ => reset_lookup_decl m 493 (by omega)
  | ⟨3, _⟩, ⟨15, _⟩ => reset_lookup_decl m 498 (by omega)
  | ⟨3, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dgen (m : Manifest) : ∀ (d : DomainId) (s : Slot),
    (Hw.core m).reset.regs (Hw.dgen d s) 8
      = (m.initState.doms d).slotGen s
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 13 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 18 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 23 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 28 (by omega)
  | ⟨0, _⟩, ⟨4, _⟩ => reset_lookup_decl m 33 (by omega)
  | ⟨0, _⟩, ⟨5, _⟩ => reset_lookup_decl m 38 (by omega)
  | ⟨0, _⟩, ⟨6, _⟩ => reset_lookup_decl m 43 (by omega)
  | ⟨0, _⟩, ⟨7, _⟩ => reset_lookup_decl m 48 (by omega)
  | ⟨0, _⟩, ⟨8, _⟩ => reset_lookup_decl m 53 (by omega)
  | ⟨0, _⟩, ⟨9, _⟩ => reset_lookup_decl m 58 (by omega)
  | ⟨0, _⟩, ⟨10, _⟩ => reset_lookup_decl m 63 (by omega)
  | ⟨0, _⟩, ⟨11, _⟩ => reset_lookup_decl m 68 (by omega)
  | ⟨0, _⟩, ⟨12, _⟩ => reset_lookup_decl m 73 (by omega)
  | ⟨0, _⟩, ⟨13, _⟩ => reset_lookup_decl m 78 (by omega)
  | ⟨0, _⟩, ⟨14, _⟩ => reset_lookup_decl m 83 (by omega)
  | ⟨0, _⟩, ⟨15, _⟩ => reset_lookup_decl m 88 (by omega)
  | ⟨0, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 150 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 155 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 160 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 165 (by omega)
  | ⟨1, _⟩, ⟨4, _⟩ => reset_lookup_decl m 170 (by omega)
  | ⟨1, _⟩, ⟨5, _⟩ => reset_lookup_decl m 175 (by omega)
  | ⟨1, _⟩, ⟨6, _⟩ => reset_lookup_decl m 180 (by omega)
  | ⟨1, _⟩, ⟨7, _⟩ => reset_lookup_decl m 185 (by omega)
  | ⟨1, _⟩, ⟨8, _⟩ => reset_lookup_decl m 190 (by omega)
  | ⟨1, _⟩, ⟨9, _⟩ => reset_lookup_decl m 195 (by omega)
  | ⟨1, _⟩, ⟨10, _⟩ => reset_lookup_decl m 200 (by omega)
  | ⟨1, _⟩, ⟨11, _⟩ => reset_lookup_decl m 205 (by omega)
  | ⟨1, _⟩, ⟨12, _⟩ => reset_lookup_decl m 210 (by omega)
  | ⟨1, _⟩, ⟨13, _⟩ => reset_lookup_decl m 215 (by omega)
  | ⟨1, _⟩, ⟨14, _⟩ => reset_lookup_decl m 220 (by omega)
  | ⟨1, _⟩, ⟨15, _⟩ => reset_lookup_decl m 225 (by omega)
  | ⟨1, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 287 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 292 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 297 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 302 (by omega)
  | ⟨2, _⟩, ⟨4, _⟩ => reset_lookup_decl m 307 (by omega)
  | ⟨2, _⟩, ⟨5, _⟩ => reset_lookup_decl m 312 (by omega)
  | ⟨2, _⟩, ⟨6, _⟩ => reset_lookup_decl m 317 (by omega)
  | ⟨2, _⟩, ⟨7, _⟩ => reset_lookup_decl m 322 (by omega)
  | ⟨2, _⟩, ⟨8, _⟩ => reset_lookup_decl m 327 (by omega)
  | ⟨2, _⟩, ⟨9, _⟩ => reset_lookup_decl m 332 (by omega)
  | ⟨2, _⟩, ⟨10, _⟩ => reset_lookup_decl m 337 (by omega)
  | ⟨2, _⟩, ⟨11, _⟩ => reset_lookup_decl m 342 (by omega)
  | ⟨2, _⟩, ⟨12, _⟩ => reset_lookup_decl m 347 (by omega)
  | ⟨2, _⟩, ⟨13, _⟩ => reset_lookup_decl m 352 (by omega)
  | ⟨2, _⟩, ⟨14, _⟩ => reset_lookup_decl m 357 (by omega)
  | ⟨2, _⟩, ⟨15, _⟩ => reset_lookup_decl m 362 (by omega)
  | ⟨2, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 424 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 429 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 434 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 439 (by omega)
  | ⟨3, _⟩, ⟨4, _⟩ => reset_lookup_decl m 444 (by omega)
  | ⟨3, _⟩, ⟨5, _⟩ => reset_lookup_decl m 449 (by omega)
  | ⟨3, _⟩, ⟨6, _⟩ => reset_lookup_decl m 454 (by omega)
  | ⟨3, _⟩, ⟨7, _⟩ => reset_lookup_decl m 459 (by omega)
  | ⟨3, _⟩, ⟨8, _⟩ => reset_lookup_decl m 464 (by omega)
  | ⟨3, _⟩, ⟨9, _⟩ => reset_lookup_decl m 469 (by omega)
  | ⟨3, _⟩, ⟨10, _⟩ => reset_lookup_decl m 474 (by omega)
  | ⟨3, _⟩, ⟨11, _⟩ => reset_lookup_decl m 479 (by omega)
  | ⟨3, _⟩, ⟨12, _⟩ => reset_lookup_decl m 484 (by omega)
  | ⟨3, _⟩, ⟨13, _⟩ => reset_lookup_decl m 489 (by omega)
  | ⟨3, _⟩, ⟨14, _⟩ => reset_lookup_decl m 494 (by omega)
  | ⟨3, _⟩, ⟨15, _⟩ => reset_lookup_decl m 499 (by omega)
  | ⟨3, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dcellV (m : Manifest) : ∀ (d : DomainId) (l : LineageId),
    (Hw.core m).reset.regs (Hw.dcellV d l) 1
      = (if ((m.initState.doms d).lineage l).isSome then 1 else 0)
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 89 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 91 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 93 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 95 (by omega)
  | ⟨0, _⟩, ⟨4, _⟩ => reset_lookup_decl m 97 (by omega)
  | ⟨0, _⟩, ⟨5, _⟩ => reset_lookup_decl m 99 (by omega)
  | ⟨0, _⟩, ⟨6, _⟩ => reset_lookup_decl m 101 (by omega)
  | ⟨0, _⟩, ⟨7, _⟩ => reset_lookup_decl m 103 (by omega)
  | ⟨0, _⟩, ⟨8, _⟩ => reset_lookup_decl m 105 (by omega)
  | ⟨0, _⟩, ⟨9, _⟩ => reset_lookup_decl m 107 (by omega)
  | ⟨0, _⟩, ⟨10, _⟩ => reset_lookup_decl m 109 (by omega)
  | ⟨0, _⟩, ⟨11, _⟩ => reset_lookup_decl m 111 (by omega)
  | ⟨0, _⟩, ⟨12, _⟩ => reset_lookup_decl m 113 (by omega)
  | ⟨0, _⟩, ⟨13, _⟩ => reset_lookup_decl m 115 (by omega)
  | ⟨0, _⟩, ⟨14, _⟩ => reset_lookup_decl m 117 (by omega)
  | ⟨0, _⟩, ⟨15, _⟩ => reset_lookup_decl m 119 (by omega)
  | ⟨0, _⟩, ⟨n+16, h⟩ => by simp [numLineage] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 226 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 228 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 230 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 232 (by omega)
  | ⟨1, _⟩, ⟨4, _⟩ => reset_lookup_decl m 234 (by omega)
  | ⟨1, _⟩, ⟨5, _⟩ => reset_lookup_decl m 236 (by omega)
  | ⟨1, _⟩, ⟨6, _⟩ => reset_lookup_decl m 238 (by omega)
  | ⟨1, _⟩, ⟨7, _⟩ => reset_lookup_decl m 240 (by omega)
  | ⟨1, _⟩, ⟨8, _⟩ => reset_lookup_decl m 242 (by omega)
  | ⟨1, _⟩, ⟨9, _⟩ => reset_lookup_decl m 244 (by omega)
  | ⟨1, _⟩, ⟨10, _⟩ => reset_lookup_decl m 246 (by omega)
  | ⟨1, _⟩, ⟨11, _⟩ => reset_lookup_decl m 248 (by omega)
  | ⟨1, _⟩, ⟨12, _⟩ => reset_lookup_decl m 250 (by omega)
  | ⟨1, _⟩, ⟨13, _⟩ => reset_lookup_decl m 252 (by omega)
  | ⟨1, _⟩, ⟨14, _⟩ => reset_lookup_decl m 254 (by omega)
  | ⟨1, _⟩, ⟨15, _⟩ => reset_lookup_decl m 256 (by omega)
  | ⟨1, _⟩, ⟨n+16, h⟩ => by simp [numLineage] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 363 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 365 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 367 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 369 (by omega)
  | ⟨2, _⟩, ⟨4, _⟩ => reset_lookup_decl m 371 (by omega)
  | ⟨2, _⟩, ⟨5, _⟩ => reset_lookup_decl m 373 (by omega)
  | ⟨2, _⟩, ⟨6, _⟩ => reset_lookup_decl m 375 (by omega)
  | ⟨2, _⟩, ⟨7, _⟩ => reset_lookup_decl m 377 (by omega)
  | ⟨2, _⟩, ⟨8, _⟩ => reset_lookup_decl m 379 (by omega)
  | ⟨2, _⟩, ⟨9, _⟩ => reset_lookup_decl m 381 (by omega)
  | ⟨2, _⟩, ⟨10, _⟩ => reset_lookup_decl m 383 (by omega)
  | ⟨2, _⟩, ⟨11, _⟩ => reset_lookup_decl m 385 (by omega)
  | ⟨2, _⟩, ⟨12, _⟩ => reset_lookup_decl m 387 (by omega)
  | ⟨2, _⟩, ⟨13, _⟩ => reset_lookup_decl m 389 (by omega)
  | ⟨2, _⟩, ⟨14, _⟩ => reset_lookup_decl m 391 (by omega)
  | ⟨2, _⟩, ⟨15, _⟩ => reset_lookup_decl m 393 (by omega)
  | ⟨2, _⟩, ⟨n+16, h⟩ => by simp [numLineage] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 500 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 502 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 504 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 506 (by omega)
  | ⟨3, _⟩, ⟨4, _⟩ => reset_lookup_decl m 508 (by omega)
  | ⟨3, _⟩, ⟨5, _⟩ => reset_lookup_decl m 510 (by omega)
  | ⟨3, _⟩, ⟨6, _⟩ => reset_lookup_decl m 512 (by omega)
  | ⟨3, _⟩, ⟨7, _⟩ => reset_lookup_decl m 514 (by omega)
  | ⟨3, _⟩, ⟨8, _⟩ => reset_lookup_decl m 516 (by omega)
  | ⟨3, _⟩, ⟨9, _⟩ => reset_lookup_decl m 518 (by omega)
  | ⟨3, _⟩, ⟨10, _⟩ => reset_lookup_decl m 520 (by omega)
  | ⟨3, _⟩, ⟨11, _⟩ => reset_lookup_decl m 522 (by omega)
  | ⟨3, _⟩, ⟨12, _⟩ => reset_lookup_decl m 524 (by omega)
  | ⟨3, _⟩, ⟨13, _⟩ => reset_lookup_decl m 526 (by omega)
  | ⟨3, _⟩, ⟨14, _⟩ => reset_lookup_decl m 528 (by omega)
  | ⟨3, _⟩, ⟨15, _⟩ => reset_lookup_decl m 530 (by omega)
  | ⟨3, _⟩, ⟨n+16, h⟩ => by simp [numLineage] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dcellPar (m : Manifest) : ∀ (d : DomainId) (l : LineageId),
    (Hw.core m).reset.regs (Hw.dcellPar d l) 14
      = (((m.initState.doms d).lineage l).map fun c => encRef c.parent).getD 0
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 90 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 92 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 94 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 96 (by omega)
  | ⟨0, _⟩, ⟨4, _⟩ => reset_lookup_decl m 98 (by omega)
  | ⟨0, _⟩, ⟨5, _⟩ => reset_lookup_decl m 100 (by omega)
  | ⟨0, _⟩, ⟨6, _⟩ => reset_lookup_decl m 102 (by omega)
  | ⟨0, _⟩, ⟨7, _⟩ => reset_lookup_decl m 104 (by omega)
  | ⟨0, _⟩, ⟨8, _⟩ => reset_lookup_decl m 106 (by omega)
  | ⟨0, _⟩, ⟨9, _⟩ => reset_lookup_decl m 108 (by omega)
  | ⟨0, _⟩, ⟨10, _⟩ => reset_lookup_decl m 110 (by omega)
  | ⟨0, _⟩, ⟨11, _⟩ => reset_lookup_decl m 112 (by omega)
  | ⟨0, _⟩, ⟨12, _⟩ => reset_lookup_decl m 114 (by omega)
  | ⟨0, _⟩, ⟨13, _⟩ => reset_lookup_decl m 116 (by omega)
  | ⟨0, _⟩, ⟨14, _⟩ => reset_lookup_decl m 118 (by omega)
  | ⟨0, _⟩, ⟨15, _⟩ => reset_lookup_decl m 120 (by omega)
  | ⟨0, _⟩, ⟨n+16, h⟩ => by simp [numLineage] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 227 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 229 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 231 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 233 (by omega)
  | ⟨1, _⟩, ⟨4, _⟩ => reset_lookup_decl m 235 (by omega)
  | ⟨1, _⟩, ⟨5, _⟩ => reset_lookup_decl m 237 (by omega)
  | ⟨1, _⟩, ⟨6, _⟩ => reset_lookup_decl m 239 (by omega)
  | ⟨1, _⟩, ⟨7, _⟩ => reset_lookup_decl m 241 (by omega)
  | ⟨1, _⟩, ⟨8, _⟩ => reset_lookup_decl m 243 (by omega)
  | ⟨1, _⟩, ⟨9, _⟩ => reset_lookup_decl m 245 (by omega)
  | ⟨1, _⟩, ⟨10, _⟩ => reset_lookup_decl m 247 (by omega)
  | ⟨1, _⟩, ⟨11, _⟩ => reset_lookup_decl m 249 (by omega)
  | ⟨1, _⟩, ⟨12, _⟩ => reset_lookup_decl m 251 (by omega)
  | ⟨1, _⟩, ⟨13, _⟩ => reset_lookup_decl m 253 (by omega)
  | ⟨1, _⟩, ⟨14, _⟩ => reset_lookup_decl m 255 (by omega)
  | ⟨1, _⟩, ⟨15, _⟩ => reset_lookup_decl m 257 (by omega)
  | ⟨1, _⟩, ⟨n+16, h⟩ => by simp [numLineage] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 364 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 366 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 368 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 370 (by omega)
  | ⟨2, _⟩, ⟨4, _⟩ => reset_lookup_decl m 372 (by omega)
  | ⟨2, _⟩, ⟨5, _⟩ => reset_lookup_decl m 374 (by omega)
  | ⟨2, _⟩, ⟨6, _⟩ => reset_lookup_decl m 376 (by omega)
  | ⟨2, _⟩, ⟨7, _⟩ => reset_lookup_decl m 378 (by omega)
  | ⟨2, _⟩, ⟨8, _⟩ => reset_lookup_decl m 380 (by omega)
  | ⟨2, _⟩, ⟨9, _⟩ => reset_lookup_decl m 382 (by omega)
  | ⟨2, _⟩, ⟨10, _⟩ => reset_lookup_decl m 384 (by omega)
  | ⟨2, _⟩, ⟨11, _⟩ => reset_lookup_decl m 386 (by omega)
  | ⟨2, _⟩, ⟨12, _⟩ => reset_lookup_decl m 388 (by omega)
  | ⟨2, _⟩, ⟨13, _⟩ => reset_lookup_decl m 390 (by omega)
  | ⟨2, _⟩, ⟨14, _⟩ => reset_lookup_decl m 392 (by omega)
  | ⟨2, _⟩, ⟨15, _⟩ => reset_lookup_decl m 394 (by omega)
  | ⟨2, _⟩, ⟨n+16, h⟩ => by simp [numLineage] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 501 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 503 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 505 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 507 (by omega)
  | ⟨3, _⟩, ⟨4, _⟩ => reset_lookup_decl m 509 (by omega)
  | ⟨3, _⟩, ⟨5, _⟩ => reset_lookup_decl m 511 (by omega)
  | ⟨3, _⟩, ⟨6, _⟩ => reset_lookup_decl m 513 (by omega)
  | ⟨3, _⟩, ⟨7, _⟩ => reset_lookup_decl m 515 (by omega)
  | ⟨3, _⟩, ⟨8, _⟩ => reset_lookup_decl m 517 (by omega)
  | ⟨3, _⟩, ⟨9, _⟩ => reset_lookup_decl m 519 (by omega)
  | ⟨3, _⟩, ⟨10, _⟩ => reset_lookup_decl m 521 (by omega)
  | ⟨3, _⟩, ⟨11, _⟩ => reset_lookup_decl m 523 (by omega)
  | ⟨3, _⟩, ⟨12, _⟩ => reset_lookup_decl m 525 (by omega)
  | ⟨3, _⟩, ⟨13, _⟩ => reset_lookup_decl m 527 (by omega)
  | ⟨3, _⟩, ⟨14, _⟩ => reset_lookup_decl m 529 (by omega)
  | ⟨3, _⟩, ⟨15, _⟩ => reset_lookup_decl m 531 (by omega)
  | ⟨3, _⟩, ⟨n+16, h⟩ => by simp [numLineage] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_drgnV (m : Manifest) : ∀ (d : DomainId) (r : RegionId),
    (Hw.core m).reset.regs (Hw.drgnV d r) 1
      = (if ((m.initState.doms d).regions r).isSome then 1 else 0)
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 121 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 123 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 125 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 127 (by omega)
  | ⟨0, _⟩, ⟨n+4, h⟩ => by simp [numRegions] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 258 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 260 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 262 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 264 (by omega)
  | ⟨1, _⟩, ⟨n+4, h⟩ => by simp [numRegions] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 395 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 397 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 399 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 401 (by omega)
  | ⟨2, _⟩, ⟨n+4, h⟩ => by simp [numRegions] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 532 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 534 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 536 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 538 (by omega)
  | ⟨3, _⟩, ⟨n+4, h⟩ => by simp [numRegions] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_drgn (m : Manifest) : ∀ (d : DomainId) (r : RegionId),
    (Hw.core m).reset.regs (Hw.drgn d r) 42
      = (((m.initState.doms d).regions r).map encRegion).getD 0
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 122 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 124 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 126 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 128 (by omega)
  | ⟨0, _⟩, ⟨n+4, h⟩ => by simp [numRegions] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 259 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 261 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 263 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 265 (by omega)
  | ⟨1, _⟩, ⟨n+4, h⟩ => by simp [numRegions] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 396 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 398 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 400 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 402 (by omega)
  | ⟨2, _⟩, ⟨n+4, h⟩ => by simp [numRegions] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 533 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 535 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 537 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 539 (by omega)
  | ⟨3, _⟩, ⟨n+4, h⟩ => by simp [numRegions] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_drunG (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.drunG d) 2
      = encRunG (m.initState.doms d).run
  | ⟨0, _⟩ => reset_lookup_decl m 130 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 267 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 404 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 541 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dsrvV (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.dsrvV d) 1
      = (if (m.initState.doms d).serving.isSome then 1 else 0)
  | ⟨0, _⟩ => reset_lookup_decl m 131 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 268 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 405 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 542 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dsrv (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.dsrv d) 2
      = (((m.initState.doms d).serving.map fun g => BitVec.ofNat 2 g.val).getD 0)
  | ⟨0, _⟩ => reset_lookup_decl m 132 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 269 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 406 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 543 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dcause (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.dcause d) 32
      = (m.initState.doms d).cause
  | ⟨0, _⟩ => reset_lookup_decl m 133 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 270 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 407 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 544 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dbudget (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.dbudget d) 32
      = BitVec.ofNat 32 (m.initState.doms d).budget
  | ⟨0, _⟩ => reset_lookup_decl m 134 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 271 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 408 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 545 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dmaxdon (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.dmaxdon d) 32
      = BitVec.ofNat 32 (m.initState.doms d).maxDonation
  | ⟨0, _⟩ => reset_lookup_decl m 135 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 272 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 409 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 546 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

end Machines.Lnp64u.Theorems.RMC
