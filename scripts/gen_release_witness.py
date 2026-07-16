#!/usr/bin/env python3
"""Generate a balanced Lean SSA witness from canonical Loom µVerilog.

This tool is intentionally untrusted: its output is accepted only when Lean's
kernel checks the renderer and semantic certificates generated around it.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


def q(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def rhs(text: str) -> str:
    patterns = [
        (r"(\d+)'d(\d+)", lambda m: f".lit {m[1]} {m[2]}"),
        (r"~([A-Za-z_]\w*)", lambda m: f".not {q(m[1])}"),
        (r"\$signed\((\w+)\) < \$signed\((\w+)\)",
         lambda m: f".slt {q(m[1])} {q(m[2])}"),
        (r"\{\{(\d+)\{(\w+)\[(\d+)\]\}\}, (\w+)\}",
         lambda m: f".sext {m[1]} {q(m[2])} {m[3]}" if m[2] == m[4]
         else (_ for _ in ()).throw(ValueError("mismatched sext operand"))),
        (r"(\w+)\[(\d+):(\d+)\]",
         lambda m: f".slice {q(m[1])} {m[2]} {m[3]}"),
        (r"(\w+)\[(\w+)\]", lambda m: f".memRead {q(m[1])} {q(m[2])}"),
        (r"(\w+) \? (\w+) : (\w+)",
         lambda m: f".mux {q(m[1])} {q(m[2])} {q(m[3])}"),
    ]
    operators = {"&": "and", "|": "or", "^": "xor", "+": "add",
                 "-": "sub", "<<": "shl", ">>": "shr", "==": "eq",
                 "<": "ult"}
    for token in ("<<", ">>", "==", "&", "|", "^", "+", "-", "<"):
        escaped = re.escape(token)
        patterns.append((rf"(\w+) {escaped} (\w+)",
                         lambda m, op=operators[token]:
                         f".bin .{op} {q(m[1])} {q(m[2])}"))
    patterns.append((r"([A-Za-z_]\w*)", lambda m: f".ident {q(m[1])}"))
    for pattern, build in patterns:
        match = re.fullmatch(pattern, text)
        if match:
            return build(match)
    raise ValueError(f"unsupported RHS: {text}")


def balanced(names: list[str], empty: str) -> str:
    if not names:
        return empty
    level = names
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), 2):
            nxt.append(level[i] if i + 1 == len(level)
                       else f".node ({level[i]}) ({level[i + 1]})")
        level = nxt
    return level[0]


def chunks(values: list, size: int) -> list[list]:
    return [values[i:i + size] for i in range(0, len(values), size)] or [[]]


def parse(path: Path) -> dict:
    lines = path.read_text().splitlines()
    module = re.fullmatch(r"module (\w+)\(", lines[0]).group(1)
    i = 2
    assert lines[1] == "  input wire clk,"
    assert lines[i].startswith("  input wire rst")
    outputs = []
    i += 1
    while lines[i] != ");":
        match = re.fullmatch(r"  output wire \[(\d+):0\] (\w+),?", lines[i])
        outputs.append({"name": match[2], "width": int(match[1]) + 1})
        i += 1
    i += 1
    regs = []
    while i < len(lines) and (match := re.fullmatch(
            r"  reg \[(\d+):0\] (\w+);", lines[i])):
        regs.append({"name": match[2], "width": int(match[1]) + 1})
        i += 1
    mems = []
    while i < len(lines) and (match := re.fullmatch(
            r"  reg \[(\d+):0\] (\w+) \[0:(\d+)\];", lines[i])):
        size = int(match[3]) + 1
        aw = size.bit_length() - 1
        assert 1 << aw == size
        mems.append({"name": match[2], "dataWidth": int(match[1]) + 1,
                     "addrWidth": aw, "init": [], "writes": []})
        i += 1
    for mem in mems:
        assert lines[i] == "  initial begin"
        i += 1
        for address in range(1 << mem["addrWidth"]):
            match = re.fullmatch(
                rf"    {re.escape(mem['name'])}\[{address}\] = "
                rf"{mem['dataWidth']}'d(\d+);", lines[i])
            if not match:
                raise ValueError(f"bad init line {i + 1}: {lines[i]}")
            mem["init"].append(int(match[1]))
            i += 1
        assert lines[i] == "  end"
        i += 1
    wires = []
    while i < len(lines) and (match := re.fullmatch(
            r"  wire \[(\d+):0\] (\w+) = (.*);", lines[i])):
        wires.append({"width": int(match[1]) + 1, "name": match[2],
                      "rhs": rhs(match[3])})
        i += 1
    assert lines[i] == "  always @(posedge clk) begin"; i += 1
    assert lines[i] == "    if (rst) begin"; i += 1
    for reg in regs:
        match = re.fullmatch(
            rf"      {re.escape(reg['name'])} <= {reg['width']}'d(\d+);", lines[i])
        reg["init"] = int(match[1]); i += 1
    assert lines[i] == "    end else begin"; i += 1
    for reg in regs:
        match = re.fullmatch(rf"      {re.escape(reg['name'])} <= (\w+);", lines[i])
        reg["next"] = match[1]; i += 1
    by_name = {mem["name"]: mem for mem in mems}
    while lines[i].startswith("      if ("):
        match = re.fullmatch(r"      if \((\w+)\) (\w+)\[(\w+)\] <= (\w+);", lines[i])
        by_name[match[2]]["writes"].append(
            {"en": match[1], "addr": match[3], "data": match[4]})
        i += 1
    assert lines[i] == "    end"; i += 1
    assert lines[i] == "  end"; i += 1
    for out in outputs:
        match = re.fullmatch(rf"  assign {re.escape(out['name'])} = (\w+);", lines[i])
        out["value"] = match[1]; i += 1
    assert lines[i:] == ["endmodule"]
    return {"name": module, "regs": regs, "mems": mems,
            "wires": wires, "outs": outputs}


def emit(data: dict, output: Path, block_size: int) -> None:
    out = ["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
           "import Loom.Release.Certificate", "", "namespace Loom.GeneratedRelease",
           "", "open Loom.Release Loom.Release.SSA", ""]
    wire_names = []
    for index, block in enumerate(chunks(data["wires"], block_size)):
        name = f"wireBlock{index:04d}"
        wire_names.append(name)
        entries = [f"  {{ width := {w['width']}, name := {q(w['name'])}, rhs := {w['rhs']} }}"
                   for w in block]
        out += [f"def {name} : List Wire := [", ",\n".join(entries), "]", ""]
    out += ["def wireTree : Rope (List Wire) :=",
            "  " + balanced(wire_names, ".leaf []").replace(
                "wireBlock", ".leaf wireBlock"), ""]
    mem_names = []
    for mi, mem in enumerate(data["mems"]):
        init_names = []
        for bi, block in enumerate(chunks(mem["init"], block_size)):
            name = f"mem{mi}Init{bi:04d}"
            init_names.append(name)
            out += [f"def {name} : List Nat := [{', '.join(map(str, block))}]", ""]
        tree = balanced(init_names, ".leaf []").replace("mem", ".leaf mem")
        writes = ", ".join(
            f"{{ en := {q(w['en'])}, addr := {q(w['addr'])}, data := {q(w['data'])} }}"
            for w in mem["writes"])
        name = f"mem{mi}"
        mem_names.append(name)
        out += [f"def {name} : Mem where", f"  name := {q(mem['name'])}",
                f"  addrWidth := {mem['addrWidth']}", f"  dataWidth := {mem['dataWidth']}",
                f"  init := {tree}", f"  writes := [{writes}]", ""]
    regs = ",\n".join(
        f"  {{ name := {q(r['name'])}, width := {r['width']}, init := {r['init']}, next := {q(r['next'])} }}"
        for r in data["regs"])
    outs = ",\n".join(
        f"  {{ name := {q(o['name'])}, width := {o['width']}, value := {q(o['value'])} }}"
        for o in data["outs"])
    out += ["def program : Program where", f"  name := {q(data['name'])}",
            "  regs := [", regs, "  ]", f"  mems := [{', '.join(mem_names)}]",
            "  wires := wireTree", "  outs := [", outs, "  ]", "",
            "#guard program.elaborate |>.isSome", "", "end Loom.GeneratedRelease", ""]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(out))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--block-size", type=int, default=512)
    args = parser.parse_args()
    emit(parse(args.input), args.output, args.block_size)


if __name__ == "__main__":
    main()
