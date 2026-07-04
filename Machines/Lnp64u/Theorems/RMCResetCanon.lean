-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
import Machines.Lnp64u.Theorems.RMCResetDeclList

/-!
# R-MC support: reset lookup arms for canonical encodings

Small reset table needed by `RMC.coupled_reset`.
-/

namespace Machines.Lnp64u.Theorems.RMC

open Machines.Lnp64u Loom.Hw Machines.Lnp64u.Hw


set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dcapV (m : Manifest) : ∀ (d : DomainId) (s : Slot),
    (Hw.core m).reset.regs (Hw.dcapV d s) 1
      = (if (((m.initState.doms d).caps s).isSome) then 1 else 0)
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 9 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 14 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 19 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 24 (by omega)
  | ⟨0, _⟩, ⟨4, _⟩ => reset_lookup_decl m 29 (by omega)
  | ⟨0, _⟩, ⟨5, _⟩ => reset_lookup_decl m 34 (by omega)
  | ⟨0, _⟩, ⟨6, _⟩ => reset_lookup_decl m 39 (by omega)
  | ⟨0, _⟩, ⟨7, _⟩ => reset_lookup_decl m 44 (by omega)
  | ⟨0, _⟩, ⟨8, _⟩ => reset_lookup_decl m 49 (by omega)
  | ⟨0, _⟩, ⟨9, _⟩ => reset_lookup_decl m 54 (by omega)
  | ⟨0, _⟩, ⟨10, _⟩ => reset_lookup_decl m 59 (by omega)
  | ⟨0, _⟩, ⟨11, _⟩ => reset_lookup_decl m 64 (by omega)
  | ⟨0, _⟩, ⟨12, _⟩ => reset_lookup_decl m 69 (by omega)
  | ⟨0, _⟩, ⟨13, _⟩ => reset_lookup_decl m 74 (by omega)
  | ⟨0, _⟩, ⟨14, _⟩ => reset_lookup_decl m 79 (by omega)
  | ⟨0, _⟩, ⟨15, _⟩ => reset_lookup_decl m 84 (by omega)
  | ⟨0, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 146 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 151 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 156 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 161 (by omega)
  | ⟨1, _⟩, ⟨4, _⟩ => reset_lookup_decl m 166 (by omega)
  | ⟨1, _⟩, ⟨5, _⟩ => reset_lookup_decl m 171 (by omega)
  | ⟨1, _⟩, ⟨6, _⟩ => reset_lookup_decl m 176 (by omega)
  | ⟨1, _⟩, ⟨7, _⟩ => reset_lookup_decl m 181 (by omega)
  | ⟨1, _⟩, ⟨8, _⟩ => reset_lookup_decl m 186 (by omega)
  | ⟨1, _⟩, ⟨9, _⟩ => reset_lookup_decl m 191 (by omega)
  | ⟨1, _⟩, ⟨10, _⟩ => reset_lookup_decl m 196 (by omega)
  | ⟨1, _⟩, ⟨11, _⟩ => reset_lookup_decl m 201 (by omega)
  | ⟨1, _⟩, ⟨12, _⟩ => reset_lookup_decl m 206 (by omega)
  | ⟨1, _⟩, ⟨13, _⟩ => reset_lookup_decl m 211 (by omega)
  | ⟨1, _⟩, ⟨14, _⟩ => reset_lookup_decl m 216 (by omega)
  | ⟨1, _⟩, ⟨15, _⟩ => reset_lookup_decl m 221 (by omega)
  | ⟨1, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 283 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 288 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 293 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 298 (by omega)
  | ⟨2, _⟩, ⟨4, _⟩ => reset_lookup_decl m 303 (by omega)
  | ⟨2, _⟩, ⟨5, _⟩ => reset_lookup_decl m 308 (by omega)
  | ⟨2, _⟩, ⟨6, _⟩ => reset_lookup_decl m 313 (by omega)
  | ⟨2, _⟩, ⟨7, _⟩ => reset_lookup_decl m 318 (by omega)
  | ⟨2, _⟩, ⟨8, _⟩ => reset_lookup_decl m 323 (by omega)
  | ⟨2, _⟩, ⟨9, _⟩ => reset_lookup_decl m 328 (by omega)
  | ⟨2, _⟩, ⟨10, _⟩ => reset_lookup_decl m 333 (by omega)
  | ⟨2, _⟩, ⟨11, _⟩ => reset_lookup_decl m 338 (by omega)
  | ⟨2, _⟩, ⟨12, _⟩ => reset_lookup_decl m 343 (by omega)
  | ⟨2, _⟩, ⟨13, _⟩ => reset_lookup_decl m 348 (by omega)
  | ⟨2, _⟩, ⟨14, _⟩ => reset_lookup_decl m 353 (by omega)
  | ⟨2, _⟩, ⟨15, _⟩ => reset_lookup_decl m 358 (by omega)
  | ⟨2, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 420 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 425 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 430 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 435 (by omega)
  | ⟨3, _⟩, ⟨4, _⟩ => reset_lookup_decl m 440 (by omega)
  | ⟨3, _⟩, ⟨5, _⟩ => reset_lookup_decl m 445 (by omega)
  | ⟨3, _⟩, ⟨6, _⟩ => reset_lookup_decl m 450 (by omega)
  | ⟨3, _⟩, ⟨7, _⟩ => reset_lookup_decl m 455 (by omega)
  | ⟨3, _⟩, ⟨8, _⟩ => reset_lookup_decl m 460 (by omega)
  | ⟨3, _⟩, ⟨9, _⟩ => reset_lookup_decl m 465 (by omega)
  | ⟨3, _⟩, ⟨10, _⟩ => reset_lookup_decl m 470 (by omega)
  | ⟨3, _⟩, ⟨11, _⟩ => reset_lookup_decl m 475 (by omega)
  | ⟨3, _⟩, ⟨12, _⟩ => reset_lookup_decl m 480 (by omega)
  | ⟨3, _⟩, ⟨13, _⟩ => reset_lookup_decl m 485 (by omega)
  | ⟨3, _⟩, ⟨14, _⟩ => reset_lookup_decl m 490 (by omega)
  | ⟨3, _⟩, ⟨15, _⟩ => reset_lookup_decl m 495 (by omega)
  | ⟨3, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_dcapKind (m : Manifest) : ∀ (d : DomainId) (s : Slot),
    (Hw.core m).reset.regs (Hw.dcapKind d s) 32
      = ((((m.initState.doms d).caps s).map fun c => encKind c.kind).getD 0)
  | ⟨0, _⟩, ⟨0, _⟩ => reset_lookup_decl m 10 (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => reset_lookup_decl m 15 (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => reset_lookup_decl m 20 (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ => reset_lookup_decl m 25 (by omega)
  | ⟨0, _⟩, ⟨4, _⟩ => reset_lookup_decl m 30 (by omega)
  | ⟨0, _⟩, ⟨5, _⟩ => reset_lookup_decl m 35 (by omega)
  | ⟨0, _⟩, ⟨6, _⟩ => reset_lookup_decl m 40 (by omega)
  | ⟨0, _⟩, ⟨7, _⟩ => reset_lookup_decl m 45 (by omega)
  | ⟨0, _⟩, ⟨8, _⟩ => reset_lookup_decl m 50 (by omega)
  | ⟨0, _⟩, ⟨9, _⟩ => reset_lookup_decl m 55 (by omega)
  | ⟨0, _⟩, ⟨10, _⟩ => reset_lookup_decl m 60 (by omega)
  | ⟨0, _⟩, ⟨11, _⟩ => reset_lookup_decl m 65 (by omega)
  | ⟨0, _⟩, ⟨12, _⟩ => reset_lookup_decl m 70 (by omega)
  | ⟨0, _⟩, ⟨13, _⟩ => reset_lookup_decl m 75 (by omega)
  | ⟨0, _⟩, ⟨14, _⟩ => reset_lookup_decl m 80 (by omega)
  | ⟨0, _⟩, ⟨15, _⟩ => reset_lookup_decl m 85 (by omega)
  | ⟨0, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨1, _⟩, ⟨0, _⟩ => reset_lookup_decl m 147 (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => reset_lookup_decl m 152 (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => reset_lookup_decl m 157 (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => reset_lookup_decl m 162 (by omega)
  | ⟨1, _⟩, ⟨4, _⟩ => reset_lookup_decl m 167 (by omega)
  | ⟨1, _⟩, ⟨5, _⟩ => reset_lookup_decl m 172 (by omega)
  | ⟨1, _⟩, ⟨6, _⟩ => reset_lookup_decl m 177 (by omega)
  | ⟨1, _⟩, ⟨7, _⟩ => reset_lookup_decl m 182 (by omega)
  | ⟨1, _⟩, ⟨8, _⟩ => reset_lookup_decl m 187 (by omega)
  | ⟨1, _⟩, ⟨9, _⟩ => reset_lookup_decl m 192 (by omega)
  | ⟨1, _⟩, ⟨10, _⟩ => reset_lookup_decl m 197 (by omega)
  | ⟨1, _⟩, ⟨11, _⟩ => reset_lookup_decl m 202 (by omega)
  | ⟨1, _⟩, ⟨12, _⟩ => reset_lookup_decl m 207 (by omega)
  | ⟨1, _⟩, ⟨13, _⟩ => reset_lookup_decl m 212 (by omega)
  | ⟨1, _⟩, ⟨14, _⟩ => reset_lookup_decl m 217 (by omega)
  | ⟨1, _⟩, ⟨15, _⟩ => reset_lookup_decl m 222 (by omega)
  | ⟨1, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨2, _⟩, ⟨0, _⟩ => reset_lookup_decl m 284 (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => reset_lookup_decl m 289 (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => reset_lookup_decl m 294 (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => reset_lookup_decl m 299 (by omega)
  | ⟨2, _⟩, ⟨4, _⟩ => reset_lookup_decl m 304 (by omega)
  | ⟨2, _⟩, ⟨5, _⟩ => reset_lookup_decl m 309 (by omega)
  | ⟨2, _⟩, ⟨6, _⟩ => reset_lookup_decl m 314 (by omega)
  | ⟨2, _⟩, ⟨7, _⟩ => reset_lookup_decl m 319 (by omega)
  | ⟨2, _⟩, ⟨8, _⟩ => reset_lookup_decl m 324 (by omega)
  | ⟨2, _⟩, ⟨9, _⟩ => reset_lookup_decl m 329 (by omega)
  | ⟨2, _⟩, ⟨10, _⟩ => reset_lookup_decl m 334 (by omega)
  | ⟨2, _⟩, ⟨11, _⟩ => reset_lookup_decl m 339 (by omega)
  | ⟨2, _⟩, ⟨12, _⟩ => reset_lookup_decl m 344 (by omega)
  | ⟨2, _⟩, ⟨13, _⟩ => reset_lookup_decl m 349 (by omega)
  | ⟨2, _⟩, ⟨14, _⟩ => reset_lookup_decl m 354 (by omega)
  | ⟨2, _⟩, ⟨15, _⟩ => reset_lookup_decl m 359 (by omega)
  | ⟨2, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨3, _⟩, ⟨0, _⟩ => reset_lookup_decl m 421 (by omega)
  | ⟨3, _⟩, ⟨1, _⟩ => reset_lookup_decl m 426 (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => reset_lookup_decl m 431 (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => reset_lookup_decl m 436 (by omega)
  | ⟨3, _⟩, ⟨4, _⟩ => reset_lookup_decl m 441 (by omega)
  | ⟨3, _⟩, ⟨5, _⟩ => reset_lookup_decl m 446 (by omega)
  | ⟨3, _⟩, ⟨6, _⟩ => reset_lookup_decl m 451 (by omega)
  | ⟨3, _⟩, ⟨7, _⟩ => reset_lookup_decl m 456 (by omega)
  | ⟨3, _⟩, ⟨8, _⟩ => reset_lookup_decl m 461 (by omega)
  | ⟨3, _⟩, ⟨9, _⟩ => reset_lookup_decl m 466 (by omega)
  | ⟨3, _⟩, ⟨10, _⟩ => reset_lookup_decl m 471 (by omega)
  | ⟨3, _⟩, ⟨11, _⟩ => reset_lookup_decl m 476 (by omega)
  | ⟨3, _⟩, ⟨12, _⟩ => reset_lookup_decl m 481 (by omega)
  | ⟨3, _⟩, ⟨13, _⟩ => reset_lookup_decl m 486 (by omega)
  | ⟨3, _⟩, ⟨14, _⟩ => reset_lookup_decl m 491 (by omega)
  | ⟨3, _⟩, ⟨15, _⟩ => reset_lookup_decl m 496 (by omega)
  | ⟨3, _⟩, ⟨n+16, h⟩ => by simp [numSlots] at h
  | ⟨n+4, h⟩, _ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_drun (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.drun d) 2
      = encRun (m.initState.doms d).run
  | ⟨0, _⟩ => reset_lookup_decl m 129 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 266 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 403 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 540 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem reset_drctr (m : Manifest) : ∀ (d : DomainId),
    (Hw.core m).reset.regs (Hw.drctr d) 32
      = BitVec.ofNat 32 (m.initState.cycle.toNat % (m.doms d).periodP)
  | ⟨0, _⟩ => reset_lookup_decl m 136 (by omega)
  | ⟨1, _⟩ => reset_lookup_decl m 273 (by omega)
  | ⟨2, _⟩ => reset_lookup_decl m 410 (by omega)
  | ⟨3, _⟩ => reset_lookup_decl m 547 (by omega)
  | ⟨n+4, h⟩ => by simp [numDomains] at h

end Machines.Lnp64u.Theorems.RMC
