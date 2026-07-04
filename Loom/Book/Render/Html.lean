-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Book.Model

/-!
# HTML renderer (L6)

Self-contained single-file HTML: inline CSS, no external assets.
-/

namespace Loom.Book.Html

def escape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

/-- Render backtick spans as `<code>`. -/
def inlineMd (s : String) : String :=
  let parts := (escape s).splitOn "`"
  (parts.zipIdx.map fun (p, i) =>
    if i % 2 == 1 then s!"<code>{p}</code>" else p).foldl (· ++ ·) ""

def renderBlock : Block → String
  | .heading l t => s!"<h{l}>{inlineMd t}</h{l}>"
  | .para c => s!"<p>{inlineMd c}</p>"
  | .table hd rows =>
      let th := String.intercalate "" (hd.map fun h => s!"<th>{inlineMd h}</th>")
      let trs := String.intercalate "\n" (rows.map fun r =>
        "<tr>" ++ String.intercalate "" (r.map fun c => s!"<td>{inlineMd c}</td>") ++ "</tr>")
      s!"<table><thead><tr>{th}</tr></thead><tbody>{trs}</tbody></table>"
  | .list items =>
      "<ul>" ++ String.intercalate "" (items.map fun i => s!"<li>{inlineMd i}</li>") ++ "</ul>"

def css : String :=
  "body{font-family:Georgia,serif;max-width:56em;margin:2em auto;padding:0 1em;\
   line-height:1.5;color:#222}code{font-family:ui-monospace,monospace;\
   background:#f4f4f4;padding:0 .2em;border-radius:3px}\
   table{border-collapse:collapse;width:100%;font-size:.95em}\
   th,td{border:1px solid #ccc;padding:.3em .6em;text-align:left}\
   th{background:#f0f0f0}h1{border-bottom:2px solid #333;padding-bottom:.2em}\
   h2{margin-top:1.6em;border-bottom:1px solid #ddd}"

def render (d : Doc) : String :=
  s!"<!DOCTYPE html><html><head><meta charset=\"utf-8\">\
     <title>{escape d.title}</title><style>{css}</style></head><body>\n" ++
  String.intercalate "\n" (d.blocks.map renderBlock) ++
  "\n</body></html>"

end Loom.Book.Html
