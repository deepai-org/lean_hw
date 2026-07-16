-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Lake
open Lake DSL

package loomConsumer

require loom from "../loom"

@[default_target]
lean_lib Consumer
