-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Lnp64u.Hw.Core
import Machines.Lnp64u.Hw.Demo

/-!
# Concrete scheduling order for the release manifest

The symbolic release checker uses this kernel theorem to expose the finite
`foldr` action tree without reducing `List.mergeSort` through well-founded
recursion. The list itself is untrusted witness data; the proof uses the
generic merge-sort theorem and a decidable pairwise-order check.
-/

namespace Machines.Lnp64u.Theorems.ReleaseOrder

@[simp] theorem schedOrderRelease :
    Machines.Lnp64u.Hw.schedOrder Machines.Lnp64u.Demo.sysManifest =
      ([0, 1, 2, 3] : List (Fin Machines.Lnp64u.numDomains)) := by
  unfold Machines.Lnp64u.Hw.schedOrder
  rw [List.mergeSort_of_pairwise (by decide)]
  decide

end Machines.Lnp64u.Theorems.ReleaseOrder
