-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.ImportJson

/-! # Fail-closed neutral import JSON regressions -/

namespace Tests.ImportJson

private def document := r#"
{
  "schema": 1,
  "module": {
    "name": "json_fixture",
    "ports": [
      {"name":"clk","direction":"input","width":1,"semantic_type":"clock","source":{"file":"fixture.v","start_line":1,"start_column":0,"end_line":1,"end_column":1}},
      {"name":"rst","direction":"input","width":1,"semantic_type":"reset","source":{"file":"fixture.v","start_line":1,"start_column":0,"end_line":1,"end_column":1}},
      {"name":"d","direction":"input","width":8,"semantic_type":"bits","source":{"file":"fixture.v","start_line":1,"start_column":0,"end_line":1,"end_column":1}},
      {"name":"q","direction":"output","width":8,"semantic_type":"bits","source":{"file":"fixture.v","start_line":1,"start_column":0,"end_line":1,"end_column":1}}
    ],
    "domains": [{"name":"core","clock_port":"clk","edge":"rising","reset":{"kind":"synchronous","port":"rst","active_high":true,"source":{"file":"fixture.v","start_line":1,"start_column":0,"end_line":1,"end_column":1}},"source":{"file":"fixture.v","start_line":1,"start_column":0,"end_line":1,"end_column":1}}],
    "registers": [{"name":"state","width":8,"init":0,"next":{"kind":"signal","width":8,"name":"d","source":{"file":"fixture.v","start_line":2,"start_column":0,"end_line":2,"end_column":1}},"source":{"file":"fixture.v","start_line":2,"start_column":0,"end_line":2,"end_column":1}}],
    "memories": [],
    "outputs": [{"name":"q","width":8,"value":{"kind":"signal","width":8,"name":"state","source":{"file":"fixture.v","start_line":3,"start_column":0,"end_line":3,"end_column":1}},"source":{"file":"fixture.v","start_line":3,"start_column":0,"end_line":3,"end_column":1}}],
    "instances": [],
    "unsupported": [],
    "source": {"file":"fixture.v","start_line":1,"start_column":0,"end_line":4,"end_column":1}
  }
}
"#

#guard match Loom.Hw.ImportJson.parseDocument document with
  | .ok module => module.lowerLocalDesign?.toOption.any fun lowered =>
      lowered.design.name == "json_fixture" && lowered.edge == .rising
  | .error _ => false

#guard match Loom.Hw.ImportJson.parseDocument
    (document.replace "\"rising\"" "\"both_edges\"") with
  | .error _ => true
  | .ok _ => false

#guard match Loom.Hw.ImportJson.parseDocument
    (document.replace "\"width\":8" "\"width\":0") with
  | .ok module => module.lowerLocalDesign?.toOption.isNone
  | .error _ => true

end Tests.ImportJson
