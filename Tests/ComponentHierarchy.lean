-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ComponentHierarchy

namespace Tests.ComponentHierarchy

open Loom.Hw Loom.Hw.ComponentHierarchy

/- These distinct paths still derive the same flattened signal. -/
#guard !namespacesDisjointB
  [{ path := "a", signals := ["b__data"], rules := [] },
   { path := "a__b", signals := ["data"], rules := [] }]

#guard namespacesDisjointB
  [{ path := "left", signals := ["data"], rules := ["step"] },
   { path := "right", signals := ["data"], rules := ["step"] }]

end Tests.ComponentHierarchy
