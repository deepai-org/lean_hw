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


def write_if_changed(path: Path, text: str) -> None:
    """Preserve mtimes so checked generated modules support incremental builds."""
    if path.exists() and path.read_text() == text:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


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


def indexed_ref(name: str) -> str:
    match = re.fullmatch(r"n(\d+)", name)
    return (f".namedWire {match[1]} {q(name)}" if match
            else f".reg {q(name)}")


def root_ref(name: str) -> str:
    """Bind a semantic/output root to its exact concrete wire spelling."""
    return indexed_ref(name)


def indexed_rhs(text: str) -> str:
    """String-free certificate view of a parsed canonical RHS."""
    patterns = [
        (r"(\d+)'d(\d+)", lambda m: f".lit {m[1]} {m[2]}"),
        (r"~([A-Za-z_]\w*)", lambda m: f".not ({indexed_ref(m[1])})"),
        (r"\$signed\((\w+)\) < \$signed\((\w+)\)",
         lambda m: f".slt ({indexed_ref(m[1])}) ({indexed_ref(m[2])})"),
        (r"\{\{(\d+)\{(\w+)\[(\d+)\]\}\}, (\w+)\}",
         lambda m: f".sext {m[1]} ({indexed_ref(m[2])}) {m[3]}" if m[2] == m[4]
         else (_ for _ in ()).throw(ValueError("mismatched sext operand"))),
        (r"(\w+)\[(\d+):(\d+)\]",
         lambda m: f".slice ({indexed_ref(m[1])}) {m[2]} {m[3]}"),
        (r"(\w+)\[(\w+)\]",
         lambda m: f".memRead {q(m[1])} ({indexed_ref(m[2])})"),
        (r"(\w+) \? (\w+) : (\w+)",
         lambda m: f".mux ({indexed_ref(m[1])}) ({indexed_ref(m[2])}) "
                   f"({indexed_ref(m[3])})"),
    ]
    operators = {"&": "and", "|": "or", "^": "xor", "+": "add",
                 "-": "sub", "<<": "shl", ">>": "shr", "==": "eq",
                 "<": "ult"}
    for token in ("<<", ">>", "==", "&", "|", "^", "+", "-", "<"):
        patterns.append((rf"(\w+) {re.escape(token)} (\w+)",
                         lambda m, op=operators[token]:
                         f".bin .{op} ({indexed_ref(m[1])}) "
                         f"({indexed_ref(m[2])})"))
    patterns.append((r"([A-Za-z_]\w*)",
                     lambda m: f".ident ({indexed_ref(m[1])})"))
    for pattern, build in patterns:
        match = re.fullmatch(pattern, text)
        if match:
            return build(match)
    raise ValueError(f"unsupported indexed RHS: {text}")


def runtime_rhs(text: str) -> dict:
    """Compact JSON form consumed by the native untrusted cert generator."""
    if match := re.fullmatch(r"(\d+)'d(\d+)", text):
        return {"op": "lit", "strings": [],
                "nums": [int(match[1]), int(match[2])]}
    if match := re.fullmatch(r"~([A-Za-z_]\w*)", text):
        return {"op": "not", "strings": [match[1]], "nums": []}
    if match := re.fullmatch(r"\$signed\((\w+)\) < \$signed\((\w+)\)", text):
        return {"op": "slt", "strings": [match[1], match[2]], "nums": []}
    if match := re.fullmatch(r"\{\{(\d+)\{(\w+)\[(\d+)\]\}\}, (\w+)\}", text):
        if match[2] != match[4]:
            raise ValueError("mismatched sext operand")
        return {"op": "sext", "strings": [match[2]],
                "nums": [int(match[1]), int(match[3])]}
    if match := re.fullmatch(r"(\w+)\[(\d+):(\d+)\]", text):
        return {"op": "slice", "strings": [match[1]],
                "nums": [int(match[2]), int(match[3])]}
    if match := re.fullmatch(r"(\w+)\[(\w+)\]", text):
        return {"op": "memRead", "strings": [match[1], match[2]], "nums": []}
    if match := re.fullmatch(r"(\w+) \? (\w+) : (\w+)", text):
        return {"op": "mux", "strings": list(match.groups()), "nums": []}
    operators = {"&": "and", "|": "or", "^": "xor", "+": "add",
                 "-": "sub", "<<": "shl", ">>": "shr", "==": "eq",
                 "<": "ult"}
    for token in ("<<", ">>", "==", "&", "|", "^", "+", "-", "<"):
        if match := re.fullmatch(rf"(\w+) {re.escape(token)} (\w+)", text):
            return {"op": operators[token], "strings": list(match.groups()),
                    "nums": []}
    if match := re.fullmatch(r"([A-Za-z_]\w*)", text):
        return {"op": "ident", "strings": [match[1]], "nums": []}
    raise ValueError(f"unsupported runtime RHS: {text}")


def rhs_fragments(text: str) -> list[str]:
    if match := re.fullmatch(r"(\d+)'d(\d+)", text):
        return [match[1], "'d", match[2], ";"]
    if match := re.fullmatch(r"~([A-Za-z_]\w*)", text):
        return ["~", match[1], ";"]
    if match := re.fullmatch(r"\$signed\((\w+)\) < \$signed\((\w+)\)", text):
        return ["$signed(", match[1], ") < $signed(", match[2], ");"]
    if match := re.fullmatch(r"\{\{(\d+)\{(\w+)\[(\d+)\]\}\}, (\w+)\}", text):
        if match[2] != match[4]:
            raise ValueError("mismatched sext operand")
        return ["{{", match[1], "{", match[2], "[", match[3],
                "]}}, ", match[4], "};"]
    if match := re.fullmatch(r"(\w+)\[(\d+):(\d+)\]", text):
        return [match[1], "[", match[2], ":", match[3], "];" ]
    if match := re.fullmatch(r"(\w+)\[(\w+)\]", text):
        return [match[1], "[", match[2], "];" ]
    if match := re.fullmatch(r"(\w+) \? (\w+) : (\w+)", text):
        return [match[1], " ? ", match[2], " : ", match[3], ";"]
    operators = ("<<", ">>", "==", "&", "|", "^", "+", "-", "<")
    for token in operators:
        if match := re.fullmatch(rf"(\w+) {re.escape(token)} (\w+)", text):
            return [match[1], " ", token, " ", match[2], ";"]
    if match := re.fullmatch(r"([A-Za-z_]\w*)", text):
        return [match[1], ";"]
    raise ValueError(f"unsupported RHS fragments: {text}")


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


def balanced_append(names: list[str], empty: str = "[]") -> str:
    """Build a logarithmic-depth List.append expression.

    Large generated programs used to put every register/output block on one
    append spine.  Rewriting through that spine made the final renderer proof
    take minutes and several GiB even though every block theorem was already
    checked.  Keep the same source order while balancing the expression tree.
    """
    if not names:
        return empty
    level = list(names)
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), 2):
            nxt.append(level[i] if i + 1 == len(level)
                       else f"({level[i]} ++ {level[i + 1]})")
        level = nxt
    return level[0]


def balanced_proof(names: list[str]) -> str:
    """Compose already named leaf equalities without reopening their proofs."""
    level = [f"congrArg Rope.leaf {name}" for name in names]
    if not level:
        return "rfl"
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), 2):
            nxt.append(level[i] if i + 1 == len(level)
                       else f"Rope.node_congr ({level[i]}) ({level[i + 1]})")
        level = nxt
    return level[0]


def balanced_node_proof(names: list[str]) -> str:
    """Compose named rope equalities whose statements already denote subtrees."""
    level = list(names)
    if not level:
        return "rfl"
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), 2):
            nxt.append(level[i] if i + 1 == len(level)
                       else f"Rope.node_congr ({level[i]}) ({level[i + 1]})")
        level = nxt
    return level[0]


def lookup_tree(entries: list[str]) -> tuple[str, str]:
    """A balanced random-access tree and its cached-size proof."""
    if len(entries) == 1:
        return f".leaf ({entries[0].strip()})", ".leaf"
    midpoint = len(entries) // 2
    left, left_ok = lookup_tree(entries[:midpoint])
    right, right_ok = lookup_tree(entries[midpoint:])
    return (f".node {midpoint} ({left}) ({right})",
            f".node rfl ({left_ok}) ({right_ok})")


def balanced_paths(count: int) -> list[list[bool]]:
    """Paths induced by `balanced`, indexed by the original leaf number."""
    level = [{index: []} for index in range(count)]
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), 2):
            if i + 1 == len(level):
                nxt.append(level[i])
                continue
            merged = {index: [False] + path
                      for index, path in level[i].items()}
            merged.update({index: [True] + path
                           for index, path in level[i + 1].items()})
            nxt.append(merged)
        level = nxt
    if not level:
        return []
    return [level[0][index] for index in range(count)]


def chunks(values: list, size: int) -> list[list]:
    return [values[i:i + size] for i in range(0, len(values), size)] or [[]]


def prelude(imports: list[str], namespace: str) -> list[str]:
    return (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT."] +
            [f"import {module}" for module in imports] +
            ["", f"namespace {namespace}", "",
             "open Loom.Release Loom.Release.SSA", "",
             "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""])


def wire_block_declarations(blocks: list[list[dict]], block_size: int,
                            first: int = 0) -> list[str]:
    out: list[str] = []
    for offset, block in enumerate(blocks):
        index = first + offset
        name = f"wireBlock{index:04d}"
        disk_name = f"diskWireBlock{index:04d}"
        proof_name = f"renderWireBlock{index:04d}"
        entries = [f"  {{ width := {w['width']}, name := {q(w['name'])}, rhs := {w['rhs']} }}"
                   for w in block]
        out += [f"def {name} : List Wire := [", ",\n".join(entries), "]", ""]
        fragment_entries = []
        for wire in block:
            fragments = (["  wire [", str(wire["width"] - 1), ":0] ",
                          wire["name"], " = "] +
                         rhs_fragments(wire["rhsText"]))
            fragment_entries.append(
                "  { fragments := [" + ", ".join(map(q, fragments)) + "] }")
        out += [f"def {disk_name} : List Line := [",
                ",\n".join(fragment_entries), "]", "",
                f"theorem {proof_name} :",
                f"    {name}.map Wire.renderLine = {disk_name} := rfl", ""]
    return out


def indexed_wire_block_declarations(blocks: list[list[dict]], block_size: int,
                                    first: int = 0) -> list[str]:
    out: list[str] = []
    for offset, block in enumerate(blocks):
        index = first + offset
        name = f"wireBlock{index:04d}"
        indexed_name = f"indexedWireBlock{index:04d}"
        # Preserve the public 128-wire lookup leaves used by action proofs,
        # but make the kernel check bounded 64-wire declarations. Internal
        # nodes compose opaque checked constants, so no parent re-reduces its
        # children and the public rope shape remains unchanged.
        check_size = 64

        def emit_checked_node(part: list[dict], raw_expr: str, base: int,
                              node_name: str, proof_name: str) -> None:
            if len(part) > check_size:
                split = len(part) // 2
                left_name = node_name + "L"
                right_name = node_name + "R"
                left_proof = proof_name + "L"
                right_proof = proof_name + "R"
                emit_checked_node(part[:split],
                                  f"(List.take {split} {raw_expr})", base,
                                  left_name, left_proof)
                emit_checked_node(part[split:],
                                  f"(List.drop {split} {raw_expr})", base + split,
                                  right_name, right_proof)
                out.extend([
                    f"def {node_name} := {left_name} ++ {right_name}", "",
                    f"theorem {proof_name} :",
                    f"    Symbolic.indexedBlockMatches "
                    f"{index * block_size + base} {raw_expr} {node_name} "
                    "= true := by",
                    f"  unfold {node_name}",
                    f"  rw [← List.take_append_drop {split} {raw_expr}]",
                    "  apply Symbolic.indexedBlockMatches_append",
                    "  · rfl",
                    f"  · exact {left_proof}",
                    f"  · exact {right_proof}", ""])
                return

            indexed_entries = [
                f"  {{ number := {index * block_size + base + item}, "
                f"width := {wire['width']}, rhs := {wire['indexedRhs']} }}"
                for item, wire in enumerate(part)]
            out.extend([f"def {node_name} : List Symbolic.IndexedWire := [",
                    ",\n".join(indexed_entries), "]", "",
                    f"theorem {proof_name} :",
                    f"    Symbolic.indexedBlockMatches "
                    f"{index * block_size + base} {raw_expr} {node_name} "
                    "= true := rfl", ""])

        block_proof = f"indexedWireBlockMatches{index:04d}"
        emit_checked_node(block, name, 0, indexed_name, block_proof)
        out += [
                f"theorem indexedWireLeafMatches{index:04d} :",
                f"    Symbolic.IndexedRopeMatches {index * block_size} " +
                  f"(.leaf {name}) (.leaf {indexed_name}) :=",
                f"  .leaf indexedWireBlockMatches{index:04d}", ""]
    return out


def fast_indexed_block_declarations(blocks: list[list[dict]], block_size: int,
                                    first: int = 0) -> list[str]:
    """String-free balanced wire data for action-certificate lookup only."""
    out: list[str] = []
    for offset, block in enumerate(blocks):
        index = first + offset
        entries = [
            f"  {{ number := {index * block_size + item}, "
            f"width := {wire['width']}, rhs := {wire['indexedRhs']} }}"
            for item, wire in enumerate(block)]
        tree, tree_ok = lookup_tree(entries)
        tree_name = f"fastIndexedWireLookupBlock{index:04d}"
        list_name = f"fastIndexedWireBlock{index:04d}"
        out += [
            f"def {tree_name} : Symbolic.LookupTree Symbolic.IndexedWire :=",
            f"  {tree}", "",
            f"def {list_name} : List Symbolic.IndexedWire :=",
            f"  {tree_name}.toList", "",
            f"theorem {tree_name}WellFormed : {tree_name}.WellFormed :=",
            f"  {tree_ok}", ""]
    return out


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
                     "addrWidth": aw, "init": [], "initLines": [],
                     "writes": []})
        i += 1
    prefix = lines[:i]
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
            mem["initLines"].append(lines[i])
            i += 1
        assert lines[i] == "  end"
        i += 1
    wires = []
    while i < len(lines) and (match := re.fullmatch(
            r"  wire \[(\d+):0\] (\w+) = (.*);", lines[i])):
        wires.append({"width": int(match[1]) + 1, "name": match[2],
                      "rhs": rhs(match[3]),
                      "rhsText": match[3],
                      "indexedRhs": indexed_rhs(match[3]),
                      "runtimeRhs": runtime_rhs(match[3]), "line": lines[i]})
        i += 1
    suffix_start = i
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
            "wires": wires, "outs": outputs, "prefix": prefix,
            "suffix": lines[suffix_start:]}


def emit(data: dict, output: Path, block_size: int) -> None:
    out = prelude(["Loom.Release.Certificate"], "Loom.GeneratedRelease")
    wire_names = []
    wire_disk_names = []
    wire_proof_names = []
    for index, block in enumerate(chunks(data["wires"], block_size)):
        name = f"wireBlock{index:04d}"
        disk_name = f"diskWireBlock{index:04d}"
        proof_name = f"renderWireBlock{index:04d}"
        wire_names.append(name)
        wire_disk_names.append(disk_name)
        wire_proof_names.append(proof_name)
        entries = [f"  {{ width := {w['width']}, name := {q(w['name'])}, rhs := {w['rhs']} }}"
                   for w in block]
        out += [f"def {name} : List Wire := [", ",\n".join(entries), "]", ""]
        disk_entries = ",\n".join(f"  {q(w['line'])}" for w in block)
        out += [f"def {disk_name} : List String := [", disk_entries, "]", "",
                f"theorem {proof_name} :",
                f"    {name}.map Wire.render = {disk_name} := rfl", ""]
    out += ["def wireTree : Rope (List Wire) :=",
            "  " + balanced(wire_names, ".leaf []").replace(
                "wireBlock", ".leaf wireBlock"), "",
            "def diskWireTree : Rope (List String) :=",
            "  " + balanced(wire_disk_names, ".leaf []").replace(
                "diskWireBlock", ".leaf diskWireBlock"), "",
            "theorem renderWireTree :",
            "    wireTree.map (fun wires => wires.map Wire.render) = diskWireTree := by",
            "  unfold wireTree diskWireTree",
            "  exact " + balanced_proof(wire_proof_names), ""]
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


def emit_program_tail(out: list[str], data: dict, block_size: int,
                      namespace: str) -> None:
    """Append memory data and the complete concrete program to a root module."""
    mem_names = []
    disk_mem_names = []
    render_mem_proofs = []
    for mi, mem in enumerate(data["mems"]):
        init_names = []
        disk_init_names = []
        render_init_proofs = []
        init_blocks = chunks(mem["init"], block_size)
        line_blocks = chunks(mem["initLines"], block_size)
        for bi, (block, line_block) in enumerate(zip(init_blocks, line_blocks)):
            name = f"mem{mi}Init{bi:04d}"
            disk_name = f"diskMem{mi}Init{bi:04d}"
            proof_name = f"renderMem{mi}Init{bi:04d}"
            init_names.append(name)
            disk_init_names.append(disk_name)
            render_init_proofs.append(proof_name)
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
        for bi, line_block in enumerate(line_blocks):
            disk_name = disk_init_names[bi]
            proof_name = render_init_proofs[bi]
            disk_entries = ",\n".join(f"  {q(line)}" for line in line_block)
            out += [f"def {disk_name} : List String := [", disk_entries, "]", "",
                    f"theorem {proof_name} :",
                    f"    {name}.renderInitLines {bi * block_size} " +
                      f"{init_names[bi]} = {disk_name} := rfl", ""]
        disk_init_tree = f"diskMem{mi}InitTree"
        out += [f"def {disk_init_tree} : Rope (List String) :=",
                "  " + balanced(disk_init_names, ".leaf []").replace(
                    "diskMem", ".leaf diskMem"), "",
                f"theorem renderMem{mi}InitTree :",
                f"    {name}.init.mapWithOffset {name}.renderInitLines 0 = " +
                  f"{disk_init_tree} := by",
                f"  unfold {name} {disk_init_tree}",
                "  exact " + balanced_proof(render_init_proofs), ""]
        disk_mem = f"diskMem{mi}Tree"
        disk_mem_names.append(disk_mem)
        render_mem_proofs.append(f"renderMem{mi}Tree")
        out += [f"def diskMem{mi}Start : List String := [\"  initial begin\"]",
                f"def diskMem{mi}End : List String := [\"  end\"]", "",
                f"def {disk_mem} : Rope (List String) :=",
                f"  .node (.leaf diskMem{mi}Start)",
                f"    (.node {disk_init_tree} (.leaf diskMem{mi}End))", "",
                f"theorem renderMem{mi}Tree : {name}.renderTree = {disk_mem} := by",
                f"  unfold SSA.Mem.renderTree {disk_mem} diskMem{mi}Start diskMem{mi}End",
                f"  exact Rope.node_congr rfl (Rope.node_congr renderMem{mi}InitTree rfl)", ""]
    regs = ",\n".join(
        f"  {{ name := {q(r['name'])}, width := {r['width']}, init := {r['init']}, next := {q(r['next'])} }}"
        for r in data["regs"])
    outs = ",\n".join(
        f"  {{ name := {q(o['name'])}, width := {o['width']}, value := {q(o['value'])} }}"
        for o in data["outs"])
    out += ["def program : Program where", f"  name := {q(data['name'])}",
            "  regs := [", regs, "  ]", f"  mems := [{', '.join(mem_names)}]",
            "  wires := wireTree", "  outs := [", outs, "  ]", ""]

    prefix_entries = ",\n".join(f"  {q(line)}" for line in data["prefix"])
    suffix_entries = ",\n".join(f"  {q(line)}" for line in data["suffix"])
    if not disk_mem_names:
        disk_mems = ".leaf []"
        mem_proof = "rfl"
    elif len(disk_mem_names) == 1:
        disk_mems = disk_mem_names[0]
        mem_proof = render_mem_proofs[0]
    else:
        # `SSA.renderMemTrees` is right-associated, unlike the balanced wire tree.
        disk_mems = disk_mem_names[-1]
        mem_proof = render_mem_proofs[-1]
        for disk_name, proof_name in reversed(list(zip(
                disk_mem_names[:-1], render_mem_proofs[:-1]))):
            disk_mems = f".node {disk_name} ({disk_mems})"
            mem_proof = f"Rope.node_congr {proof_name} ({mem_proof})"
    out += ["def diskPrefix : List String := [", prefix_entries, "]", "",
            "def diskSuffix : List String := [", suffix_entries, "]", "",
            "def diskMemTrees : Rope (List String) :=", f"  {disk_mems}", "",
            "theorem renderMemTrees : SSA.renderMemTrees program.mems = " +
              "diskMemTrees := by",
            "  unfold program SSA.renderMemTrees diskMemTrees",
            f"  exact {mem_proof}", "",
            "theorem renderPrefix : program.renderPrefix = diskPrefix := rfl", "",
            "theorem renderSuffix : program.renderSuffix = diskSuffix := rfl", "",
            "def diskTree : Rope (List String) :=",
            "  .node (.leaf diskPrefix)",
            "    (.node diskMemTrees (.node diskWireTree (.leaf diskSuffix)))", "",
            "theorem renderTree : program.renderTree = diskTree := by",
            "  unfold SSA.Program.renderTree diskTree",
            "  exact Rope.node_congr (congrArg Rope.leaf renderPrefix) " +
              "(Rope.node_congr renderMemTrees " +
              "(Rope.node_congr renderWireTree " +
              "(congrArg Rope.leaf renderSuffix)))", "",
            "theorem exactBytes : program.renderTree.flattenBytes = " +
              "diskTree.flattenBytes := Rope.flattenBytes_congr renderTree", "",
            f"end {namespace}", ""]


def emit_semantic_program(data: dict, output: Path, block_size: int,
                          indexed_root_module: str, namespace: str) -> None:
    """Emit program metadata without any disk-text/render declarations."""
    out = prelude(["Loom.Release.Certificate", indexed_root_module], namespace)
    out += ["namespace Semantic", ""]
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
                f"  addrWidth := {mem['addrWidth']}",
                f"  dataWidth := {mem['dataWidth']}", f"  init := {tree}",
                f"  writes := [{writes}]", ""]
    regs = ",\n".join(
        f"  {{ name := {q(r['name'])}, width := {r['width']}, init := {r['init']}, next := {q(r['next'])} }}"
        for r in data["regs"])
    outs = ",\n".join(
        f"  {{ name := {q(o['name'])}, width := {o['width']}, value := {q(o['value'])} }}"
        for o in data["outs"])
    out += ["def program : Program where", f"  name := {q(data['name'])}",
            "  regs := [", regs, "  ]", f"  mems := [{', '.join(mem_names)}]",
            "  wires := wireTree", "  outs := [", outs, "  ]", "",
            "end Semantic", "", f"end {namespace}", ""]
    write_if_changed(output, "\n".join(out))


def emit_batched_program(data: dict, output: Path, block_size: int,
                         namespace: str, indexed_root_module: str,
                         names: list[str], disk_names: list[str],
                         proofs: list[str], disk_chunk_names: list[str],
                         render_chunk_names: list[str]) -> list[str]:
    """Emit bounded memory/render modules and a lightweight release root."""
    prefix = ".".join(output.parent.parts)
    mem_data_modules: list[str] = []
    mem_root_modules: list[str] = []
    mem_names: list[str] = []
    disk_mem_names: list[str] = []
    render_mem_proofs: list[str] = []
    generated_modules: list[str] = []

    for mi, mem in enumerate(data["mems"]):
        data_module = f"{prefix}.MemData{mi}"
        mem_data_modules.append(data_module)
        generated_modules.append(data_module)
        init_blocks = chunks(mem["init"], block_size)
        line_blocks = chunks(mem["initLines"], block_size)
        init_names = [f"mem{mi}Init{bi:04d}" for bi in range(len(init_blocks))]
        data_out = prelude(["Loom.Release.Certificate"], namespace)
        for bi, block in enumerate(init_blocks):
            data_out += [
                f"def {init_names[bi]} : List Nat := "
                f"[{', '.join(map(str, block))}]", ""]
        tree = balanced(init_names, ".leaf []").replace("mem", ".leaf mem")
        writes = ", ".join(
            f"{{ en := {q(w['en'])}, addr := {q(w['addr'])}, "
            f"data := {q(w['data'])} }}" for w in mem["writes"])
        mem_name = f"mem{mi}"
        mem_names.append(mem_name)
        data_out += [f"def {mem_name} : Mem where",
                     f"  name := {q(mem['name'])}",
                     f"  addrWidth := {mem['addrWidth']}",
                     f"  dataWidth := {mem['dataWidth']}",
                     f"  init := {tree}", f"  writes := [{writes}]", "",
                     f"end {namespace}", ""]
        write_if_changed(output.parent / f"MemData{mi}.lean",
                         "\n".join(data_out))

        render_modules: list[str] = []
        disk_init_names: list[str] = []
        render_init_proofs: list[str] = []
        for bi, line_block in enumerate(line_blocks):
            render_module = f"{prefix}.MemRender{mi}_{bi:04d}"
            render_modules.append(render_module)
            generated_modules.append(render_module)
            disk_name = f"diskMem{mi}Init{bi:04d}"
            proof_name = f"renderMem{mi}Init{bi:04d}"
            disk_init_names.append(disk_name)
            render_init_proofs.append(proof_name)
            disk_entries = ",\n".join(f"  {q(line)}" for line in line_block)
            render_out = prelude([data_module], namespace)
            render_out += [f"def {disk_name} : List String := [",
                           disk_entries, "]", "", f"theorem {proof_name} :",
                           f"    {mem_name}.renderInitLines {bi * block_size} "
                           f"{init_names[bi]} = {disk_name} := rfl", "",
                           f"end {namespace}", ""]
            write_if_changed(output.parent / f"MemRender{mi}_{bi:04d}.lean",
                             "\n".join(render_out))

        mem_root_module = f"{prefix}.MemRoot{mi}"
        mem_root_modules.append(mem_root_module)
        generated_modules.append(mem_root_module)
        disk_init_tree = f"diskMem{mi}InitTree"
        disk_mem = f"diskMem{mi}Tree"
        disk_mem_names.append(disk_mem)
        render_mem_proofs.append(f"renderMem{mi}Tree")
        mem_root = prelude([data_module] + render_modules, namespace)
        mem_root += [f"def {disk_init_tree} : Rope (List String) :=",
                     "  " + balanced(disk_init_names, ".leaf []").replace(
                         "diskMem", ".leaf diskMem"), "",
                     f"theorem renderMem{mi}InitTree :",
                     f"    {mem_name}.init.mapWithOffset "
                     f"{mem_name}.renderInitLines 0 = {disk_init_tree} := by",
                     f"  unfold {mem_name} {disk_init_tree}",
                     "  exact " + balanced_proof(render_init_proofs), "",
                     f"def diskMem{mi}Start : List String := [\"  initial begin\"]",
                     f"def diskMem{mi}End : List String := [\"  end\"]", "",
                     f"def {disk_mem} : Rope (List String) :=",
                     f"  .node (.leaf diskMem{mi}Start)",
                     f"    (.node {disk_init_tree} (.leaf diskMem{mi}End))", "",
                     f"theorem renderMem{mi}Tree : {mem_name}.renderTree = "
                     f"{disk_mem} := by",
                     f"  unfold SSA.Mem.renderTree {disk_mem} "
                     f"diskMem{mi}Start diskMem{mi}End",
                     f"  exact Rope.node_congr rfl (Rope.node_congr "
                     f"renderMem{mi}InitTree rfl)", "", f"end {namespace}", ""]
        write_if_changed(output.parent / f"MemRoot{mi}.lean",
                         "\n".join(mem_root))

    program_module = f"{prefix}.ProgramData"
    generated_modules.append(program_module)
    program_out = prelude([indexed_root_module] + mem_data_modules, namespace)
    program_reg_blocks = []
    for bi, block in enumerate(chunks(data["regs"], 16)):
        block_name = f"programRegBlock{bi:04d}"
        program_reg_blocks.append(block_name)
        entries = ",\n".join(
            f"  {{ name := {q(r['name'])}, width := {r['width']}, "
            f"init := {r['init']}, next := {q(r['next'])} }}" for r in block)
        program_out += [f"def {block_name} : List Reg := [", entries, "]", ""]
    program_out += ["def programRegs : List Reg :=",
                    "  " + balanced_append(program_reg_blocks), ""]
    program_out_blocks = []
    for bi, block in enumerate(chunks(data["outs"], 16)):
        block_name = f"programOutBlock{bi:04d}"
        program_out_blocks.append(block_name)
        entries = ",\n".join(
            f"  {{ name := {q(o['name'])}, width := {o['width']}, "
            f"value := {q(o['value'])} }}" for o in block)
        program_out += [f"def {block_name} : List Out := [", entries, "]", ""]
    program_out += ["def programOuts : List Out :=",
                    "  " + balanced_append(program_out_blocks), ""]
    program_out += ["def program : Program where",
                    f"  name := {q(data['name'])}", "  regs := programRegs",
                    f"  mems := [{', '.join(mem_names)}]",
                    "  wires := wireTree", "  outs := programOuts", "",
                    f"end {namespace}", ""]
    write_if_changed(output.parent / "ProgramData.lean", "\n".join(program_out))

    framing_reg_modules = [
        f"{prefix}.FramingReg{bi:04d}"
        for bi in range(len(program_reg_blocks))]
    framing_out_modules = [
        f"{prefix}.FramingOut{bi:04d}"
        for bi in range(len(program_out_blocks))]
    framing_fixed_module = f"{prefix}.FramingFixed"
    generated_modules += (framing_reg_modules + framing_out_modules +
                          [framing_fixed_module])
    root = prelude([program_module, indexed_root_module, framing_fixed_module] +
                   framing_reg_modules + framing_out_modules + mem_root_modules,
                   namespace)
    root += ["def diskWireLineTree : Rope (List Line) :=",
             "  " + balanced(disk_chunk_names, ".leaf []"), "",
             "theorem renderWireLineTree :",
             "    wireTree.map (fun wires => wires.map Wire.renderLine) = "
             "diskWireLineTree := by",
             "  unfold wireTree diskWireLineTree",
             "  exact " + balanced_node_proof(render_chunk_names), "",
             "def diskWireTree : Rope (List String) :=",
             "  diskWireLineTree.map (fun lines => lines.map Line.render)", "",
             "theorem renderWireTree :",
             "    wireTree.map (fun wires => wires.map Wire.render) = "
             "diskWireTree := by", "  rw [← wireRenderTree_factor]",
             "  exact congrArg (Rope.map (fun lines => lines.map Line.render)) "
             "renderWireLineTree", ""]

    def emit_disk_list(target: list[str], name: str, lines: list[str]) -> None:
        entries = ",\n".join(f"  {q(line)}" for line in lines)
        target.extend([f"def {name} : List String := [", entries, "]", ""])

    header_count = len(data["prefix"]) - len(data["regs"]) - len(data["mems"])
    fixed_out = prelude([program_module], namespace)
    emit_disk_list(fixed_out, "diskHeader", data["prefix"][:header_count])
    disk_reg_decls: list[str] = []
    disk_reg_resets: list[str] = []
    disk_reg_nexts: list[str] = []
    reg_decl_lines = data["prefix"][header_count:header_count + len(data["regs"])]
    suffix = data["suffix"]
    reset_start = 2
    next_start = reset_start + len(data["regs"]) + 1
    for bi, _ in enumerate(program_reg_blocks):
        start = bi * 16
        end = min(start + 16, len(data["regs"]))
        decl_name = f"diskRegDeclBlock{bi:04d}"
        reset_name = f"diskRegResetBlock{bi:04d}"
        next_name = f"diskRegNextBlock{bi:04d}"
        disk_reg_decls.append(decl_name)
        disk_reg_resets.append(reset_name)
        disk_reg_nexts.append(next_name)
        block_out = prelude([program_module], namespace)
        emit_disk_list(block_out, decl_name, reg_decl_lines[start:end])
        emit_disk_list(block_out, reset_name,
                       suffix[reset_start + start:reset_start + end])
        emit_disk_list(block_out, next_name,
                       suffix[next_start + start:next_start + end])
        block_out += [f"theorem renderRegDeclBlock{bi:04d} :",
                      f"    programRegBlock{bi:04d}.map (fun reg =>",
                      "      s!\"  reg [{reg.width - 1}:0] {reg.name};\") = "
                      f"{decl_name} := rfl", "",
                      f"theorem renderRegResetBlock{bi:04d} :",
                      f"    programRegBlock{bi:04d}.map (fun reg =>",
                      "      s!\"      {reg.name} <= {reg.width}'d{reg.init};\") = "
                      f"{reset_name} := rfl", "",
                      f"theorem renderRegNextBlock{bi:04d} :",
                      f"    programRegBlock{bi:04d}.map (fun reg =>",
                      "      s!\"      {reg.name} <= {reg.next};\") = "
                      f"{next_name} := rfl", "", f"end {namespace}", ""]
        write_if_changed(output.parent / f"FramingReg{bi:04d}.lean",
                         "\n".join(block_out))
    emit_disk_list(fixed_out, "diskMemDecls",
                   data["prefix"][header_count + len(data["regs"]):])

    writes_count = sum(len(mem["writes"]) for mem in data["mems"])
    writes_start = next_start + len(data["regs"])
    outs_start = writes_start + writes_count + 2
    emit_disk_list(fixed_out, "diskAlwaysStart", suffix[:reset_start])
    emit_disk_list(fixed_out, "diskAlwaysMiddle",
                   suffix[reset_start + len(data["regs"]):next_start])
    emit_disk_list(fixed_out, "diskMemWrites",
                   suffix[writes_start:writes_start + writes_count])
    emit_disk_list(fixed_out, "diskAlwaysEnd",
                   suffix[writes_start + writes_count:outs_start])
    disk_out_blocks: list[str] = []
    for bi, _ in enumerate(program_out_blocks):
        start = bi * 16
        end = min(start + 16, len(data["outs"]))
        name = f"diskOutBlock{bi:04d}"
        disk_out_blocks.append(name)
        out_block = prelude([program_module], namespace)
        emit_disk_list(out_block, name,
                       suffix[outs_start + start:outs_start + end])
        out_block += [f"theorem renderOutBlock{bi:04d} :",
                      f"    programOutBlock{bi:04d}.map (fun out =>",
                      "      s!\"  assign {out.name} = {out.value};\") = "
                      f"{name} := rfl", "", f"end {namespace}", ""]
        write_if_changed(output.parent / f"FramingOut{bi:04d}.lean",
                         "\n".join(out_block))
    emit_disk_list(fixed_out, "diskModuleEnd", suffix[-1:])
    fixed_out += [f"end {namespace}", ""]
    write_if_changed(output.parent / "FramingFixed.lean", "\n".join(fixed_out))
    if not disk_mem_names:
        disk_mems, mem_proof = ".leaf []", "rfl"
    elif len(disk_mem_names) == 1:
        disk_mems, mem_proof = disk_mem_names[0], render_mem_proofs[0]
    else:
        disk_mems, mem_proof = disk_mem_names[-1], render_mem_proofs[-1]
        for disk_name, proof_name in reversed(list(zip(
                disk_mem_names[:-1], render_mem_proofs[:-1]))):
            disk_mems = f".node {disk_name} ({disk_mems})"
            mem_proof = f"Rope.node_congr {proof_name} ({mem_proof})"
    # Mirror the renderer's outer append structure, but keep each generated
    # collection balanced.  This lets simp/rw operate at logarithmic depth.
    disk_reg_decl_tree = balanced_append(disk_reg_decls)
    disk_reg_reset_tree = balanced_append(disk_reg_resets)
    disk_reg_next_tree = balanced_append(disk_reg_nexts)
    disk_out_tree = balanced_append(disk_out_blocks)
    root += ["def diskPrefix : List String :=",
             f"  diskHeader ++ ({disk_reg_decl_tree} ++ diskMemDecls)", "",
             "def diskSuffix : List String :=",
             f"  diskAlwaysStart ++ ({disk_reg_reset_tree} ++ "
             f"(diskAlwaysMiddle ++ ({disk_reg_next_tree} ++ "
             "(diskMemWrites ++ (diskAlwaysEnd ++ "
             f"({disk_out_tree} ++ diskModuleEnd))))))", "",
             "def diskMemTrees : Rope (List String) :=", f"  {disk_mems}", "",
             "theorem renderMemTrees : SSA.renderMemTrees program.mems = "
             "diskMemTrees := by", "  unfold program SSA.renderMemTrees "
             "diskMemTrees", f"  exact {mem_proof}", "",
             "theorem renderPrefix : program.renderPrefix = diskPrefix := by",
             "  unfold Program.renderPrefix headerLines declLines program "
             "programRegs diskPrefix",
             "  simp only [List.map_append]",
             *[f"  rw [renderRegDeclBlock{bi:04d}]"
               for bi in range(len(program_reg_blocks))],
             "  rfl", "",
             "theorem renderSuffix : program.renderSuffix = diskSuffix := by",
             "  unfold Program.renderSuffix alwaysLines program programRegs "
             "programOuts diskSuffix",
             "  simp only [List.map_append]",
             *[f"  rw [renderRegResetBlock{bi:04d}]"
               for bi in range(len(program_reg_blocks))],
             *[f"  rw [renderRegNextBlock{bi:04d}]"
               for bi in range(len(program_reg_blocks))],
             *[f"  rw [renderOutBlock{bi:04d}]"
               for bi in range(len(program_out_blocks))],
             "  rfl", "",
             "def diskTree : Rope (List String) :=",
             "  .node (.leaf diskPrefix)",
             "    (.node diskMemTrees (.node diskWireTree (.leaf diskSuffix)))", "",
             "theorem renderTree : program.renderTree = diskTree := by",
             "  unfold SSA.Program.renderTree diskTree",
             "  exact Rope.node_congr (congrArg Rope.leaf renderPrefix) "
             "(Rope.node_congr renderMemTrees (Rope.node_congr renderWireTree "
             "(congrArg Rope.leaf renderSuffix)))", "",
             "theorem exactBytes : program.renderTree.flattenBytes = "
             "diskTree.flattenBytes := Rope.flattenBytes_congr renderTree", "",
             f"end {namespace}", ""]
    write_if_changed(output, "\n".join(root))
    return generated_modules


def emit_batched(data: dict, output: Path, block_size: int,
                 batch_blocks: int, design_expr: str | None = None,
                 design_imports: list[str] | None = None) -> None:
    """Emit bounded leaf modules and a small constant-only composition root."""
    try:
        relative = output.resolve().relative_to(Path.cwd().resolve())
    except ValueError as error:
        raise ValueError("batched output must be beneath the current directory") from error
    root_module = ".".join(relative.with_suffix("").parts)
    cert_module_prefix = ".".join(relative.parent.parts)
    indexed_root_module = f"{cert_module_prefix}.IndexedRoot"
    indexed_root_path = output.parent / "IndexedRoot.lean"
    semantic_root_module = f"{cert_module_prefix}.SemanticRoot"
    semantic_root_path = output.parent / "SemanticRoot.lean"
    artifact = re.sub(r"\W", "", output.parent.name)
    namespace = f"Loom.GeneratedRelease.{artifact}"
    blocks = chunks(data["wires"], block_size)
    output.parent.mkdir(parents=True, exist_ok=True)
    batch_modules = []
    for batch_index, start in enumerate(range(0, len(blocks), batch_blocks)):
        module = ".".join(relative.parent.parts + (f"Batch{batch_index:03d}",))
        batch_modules.append(module)
        batch_path = output.parent / f"Batch{batch_index:03d}.lean"
        batch = prelude(["Loom.Release.SymbolicCertificate"], namespace)
        batch += wire_block_declarations(
            blocks[start:start + batch_blocks], block_size, first=start)
        batch += [f"end {namespace}", ""]
        write_if_changed(batch_path, "\n".join(batch))

    expected_batches = {f"Batch{i:03d}.lean" for i in range(len(batch_modules))}
    for stale in output.parent.glob("Batch*.lean"):
        if stale.name not in expected_batches:
            stale.unlink()

    indexed_batch_modules = []
    indexed_batch_blocks = batch_blocks
    for batch_index, start in enumerate(
            range(0, len(blocks), indexed_batch_blocks)):
        module = ".".join(relative.parent.parts +
                          (f"IndexedBatch{batch_index:04d}",))
        indexed_batch_modules.append(module)
        batch_path = output.parent / f"IndexedBatch{batch_index:04d}.lean"
        owner = start // batch_blocks
        batch = prelude([batch_modules[owner]], namespace)
        batch += indexed_wire_block_declarations(
            blocks[start:start + indexed_batch_blocks], block_size, first=start)
        batch += [f"end {namespace}", ""]
        write_if_changed(batch_path, "\n".join(batch))

    expected_indexed_batches = {
        f"IndexedBatch{i:04d}.lean" for i in range(len(indexed_batch_modules))}
    for stale in output.parent.glob("IndexedBatch*.lean"):
        if stale.name not in expected_indexed_batches:
            stale.unlink()

    fast_batch_modules = []
    for batch_index, start in enumerate(range(0, len(blocks), batch_blocks)):
        module = ".".join(relative.parent.parts +
                          (f"FastIndexedBatch{batch_index:03d}",))
        fast_batch_modules.append(module)
        batch_path = output.parent / f"FastIndexedBatch{batch_index:03d}.lean"
        batch = prelude(["Loom.Release.SymbolicCertificate"], namespace)
        batch += fast_indexed_block_declarations(
            blocks[start:start + batch_blocks], block_size, first=start)
        batch += [f"end {namespace}", ""]
        write_if_changed(batch_path, "\n".join(batch))

    expected_fast_batches = {
        f"FastIndexedBatch{i:03d}.lean" for i in range(len(fast_batch_modules))}
    for stale in output.parent.glob("FastIndexedBatch*.lean"):
        if stale.name not in expected_fast_batches:
            stale.unlink()

    names = [f"wireBlock{i:04d}" for i in range(len(blocks))]
    indexed_names = [f"indexedWireBlock{i:04d}" for i in range(len(blocks))]
    disk_names = [f"diskWireBlock{i:04d}" for i in range(len(blocks))]
    proofs = [f"renderWireBlock{i:04d}" for i in range(len(blocks))]
    indexed_proofs = [f"indexedWireLeafMatches{i:04d}" for i in range(len(blocks))]
    indexed_paths = balanced_paths(len(blocks))
    fast_names = [f"fastIndexedWireBlock{i:04d}"
                  for i in range(len(blocks))]
    fast_root = prelude(["Loom.Release.SymbolicCertificate"] +
                        fast_batch_modules, namespace)
    fast_root += [
        "def fastIndexedWireTree : Rope (List Symbolic.IndexedWire) :=",
        "  " + balanced(fast_names, ".leaf []").replace(
            "fastIndexedWireBlock", ".leaf fastIndexedWireBlock"), "",
        *[
            f"theorem fastIndexedWireResolveBlock{index:04d} (offset : Nat) :\n"
            "    fastIndexedWireTree.resolve? "
            f"⟨[{', '.join('true' if step else 'false' for step in path)}], "
            f"offset⟩ = fastIndexedWireBlock{index:04d}[offset]? := rfl\n"
            for index, path in enumerate(indexed_paths)
        ],
        "def fastWireTable : Symbolic.WireTable where",
        f"  leafSize := {block_size}",
        f"  leafCount := {len(blocks)}", "",
        f"end {namespace}", ""]
    write_if_changed(output.parent / "FastIndexedRoot.lean",
                     "\n".join(fast_root))

    # One balanced-path proof per wire leaf.  Action certificates later
    # specialize these opaque constants for individual mux outputs instead of
    # rechecking the global rope path for every use (over 120k uses on LNP64-u).
    lookup_evidence_batch_size = 16
    lookup_evidence_modules = []
    for batch_index, start in enumerate(
            range(0, len(blocks), lookup_evidence_batch_size)):
        module = ".".join(relative.parent.parts +
                          (f"FastLookupEvidenceBatch{batch_index:03d}",))
        lookup_evidence_modules.append(module)
        batch_path = output.parent / f"FastLookupEvidenceBatch{batch_index:03d}.lean"
        batch = prelude([f"{cert_module_prefix}.FastIndexedRoot"], namespace)
        for index in range(start, min(start + lookup_evidence_batch_size,
                                      len(blocks))):
            path = indexed_paths[index]
            path_text = ", ".join("true" if step else "false" for step in path)
            batch += [
                f"theorem fastIndexedWireLookupEvidence{index:04d} :",
                "    Symbolic.IndexedLookupBlockEvidence fastIndexedWireTree",
                f"      fastWireTable {index * block_size} "
                f"fastIndexedWireBlock{index:04d} := by",
                "  apply Symbolic.indexedLookupBlockEvidence_of_resolve",
                "      (blockIndex := " + str(index) + ")",
                f"      (path := [{path_text}])",
                "  · decide",
                "  · rfl",
                "  · decide",
                f"  · exact fastIndexedWireResolveBlock{index:04d}", ""]
        batch += [f"end {namespace}", ""]
        write_if_changed(batch_path, "\n".join(batch))

    expected_lookup_evidence = {
        f"FastLookupEvidenceBatch{i:03d}.lean"
        for i in range(len(lookup_evidence_modules))}
    for stale in output.parent.glob("FastLookupEvidenceBatch*.lean"):
        if stale.name not in expected_lookup_evidence:
            stale.unlink()
    lookup_evidence_root = prelude(lookup_evidence_modules, namespace)
    lookup_evidence_root += [f"end {namespace}", ""]
    write_if_changed(output.parent / "FastLookupEvidenceRoot.lean",
                     "\n".join(lookup_evidence_root))

    # Proof-carrying logarithmic lookup tree for kernel expression checks. The
    # computational fields are the same bounded wire blocks; each entry also
    # carries the already checked theorem connecting it to the semantic rope.
    checked_blocks = prelude(
        [f"{cert_module_prefix}.FastLookupEvidenceRoot"], namespace)
    checked_entry_names = [
        f"fastCheckedIndexedBlock{index:04d}" for index in range(len(blocks))]
    checked_tree, _ = lookup_tree(checked_entry_names)
    checked_blocks += [
        *[
            f"def {checked_entry_names[index]} : Symbolic.CheckedIndexedBlock " +
            "fastIndexedWireTree fastWireTable :=\n" +
            "  { start := " + str(index * block_size) +
            f", block := fastIndexedWireBlock{index:04d}, " +
            f"evidence := fastIndexedWireLookupEvidence{index:04d} }}\n"
            for index in range(len(blocks))
        ],
        "def fastCheckedIndexedBlocks : Symbolic.LookupTree " +
        "(Symbolic.CheckedIndexedBlock fastIndexedWireTree fastWireTable) :=",
        "  " + checked_tree, "", f"end {namespace}", ""]
    write_if_changed(output.parent / "FastCheckedIndexedBlocks.lean",
                     "\n".join(checked_blocks))

    bridge_modules = []
    bridge_names = []
    for batch_index, start in enumerate(range(0, len(blocks), batch_blocks)):
        module = ".".join(relative.parent.parts +
                          (f"FastIndexedBridgeBatch{batch_index:03d}",))
        bridge_modules.append(module)
        batch_path = output.parent / f"FastIndexedBridgeBatch{batch_index:03d}.lean"
        batch = prelude([
            ".".join(relative.parent.parts +
                     (f"IndexedBatch{batch_index:04d}",)),
            ".".join(relative.parent.parts +
                     (f"FastIndexedBatch{batch_index:03d}",))], namespace)
        for index in range(start, min(start + batch_blocks, len(blocks))):
            proof = f"fastIndexedWireBlockEq{index:04d}"
            bridge_names.append(proof)
            indexed_defs = [f"indexedWireBlock{index:04d}"]
            if len(blocks[index]) > 64:
                indexed_defs += [f"indexedWireBlock{index:04d}L",
                                 f"indexedWireBlock{index:04d}R"]
            batch += [f"theorem {proof} :",
                      f"    fastIndexedWireBlock{index:04d} = "
                      f"indexedWireBlock{index:04d} := by",
                      "  simp [" +
                      f"fastIndexedWireBlock{index:04d}, " +
                      f"fastIndexedWireLookupBlock{index:04d}, " +
                      ", ".join(indexed_defs) +
                      ", Symbolic.LookupTree.toList]", ""]
        batch += [f"end {namespace}", ""]
        write_if_changed(batch_path, "\n".join(batch))

    expected_bridge_batches = {
        f"FastIndexedBridgeBatch{i:03d}.lean"
        for i in range(len(bridge_modules))
    }
    for stale in output.parent.glob("FastIndexedBridgeBatch*.lean"):
        if stale.name not in expected_bridge_batches:
            stale.unlink()

    bridge_root = prelude([
        f"{cert_module_prefix}.IndexedRoot",
        f"{cert_module_prefix}.FastIndexedRoot",
        *bridge_modules], namespace)
    bridge_root += [
        "theorem fastIndexedWireTree_eq_indexedWireTree :",
        "    fastIndexedWireTree = indexedWireTree := by",
        "  unfold fastIndexedWireTree indexedWireTree",
        "  exact " + balanced_proof(bridge_names), "",
        f"end {namespace}", ""]
    write_if_changed(output.parent / "FastIndexedBridge.lean",
                     "\n".join(bridge_root))

    tree_chunk_modules: list[str] = []
    wire_chunk_names: list[str] = []
    indexed_chunk_names: list[str] = []
    disk_chunk_names: list[str] = []
    indexed_chunk_proofs: list[str] = []
    render_chunk_proofs: list[str] = []
    wire_chunks = chunks(list(range(len(blocks))), 16)
    for batch_index, chunk_group in enumerate(chunks(wire_chunks, 16)):
        module = f"{cert_module_prefix}.TreeChunkBatch{batch_index:03d}"
        tree_chunk_modules.append(module)
        imported = []
        for indices in chunk_group:
            for index in indices:
                owner = index // indexed_batch_blocks
                candidate = indexed_batch_modules[owner]
                if candidate not in imported:
                    imported.append(candidate)
        chunk_out = prelude(imported, namespace)
        for local_index, indices in enumerate(chunk_group):
            chunk_index = batch_index * 16 + local_index
            wire_name = f"wireTreeChunk{chunk_index:04d}"
            indexed_name = f"indexedWireTreeChunk{chunk_index:04d}"
            disk_name = f"diskWireTreeChunk{chunk_index:04d}"
            indexed_proof = f"indexedWireTreeChunkMatches{chunk_index:04d}"
            render_proof = f"renderWireTreeChunk{chunk_index:04d}"
            wire_chunk_names.append(wire_name)
            indexed_chunk_names.append(indexed_name)
            disk_chunk_names.append(disk_name)
            indexed_chunk_proofs.append(indexed_proof)
            render_chunk_proofs.append(render_proof)
            raw_tree = balanced(
                [f".leaf wireBlock{index:04d}" for index in indices],
                ".leaf []")
            indexed_tree = balanced(
                [f".leaf indexedWireBlock{index:04d}" for index in indices],
                ".leaf []")
            disk_tree = balanced(
                [f".leaf diskWireBlock{index:04d}" for index in indices],
                ".leaf []")
            chunk_out += [f"def {wire_name} : Rope (List Wire) :=",
                          f"  {raw_tree}", "",
                          f"def {indexed_name} : Rope "
                          "(List Symbolic.IndexedWire) :=",
                          f"  {indexed_tree}", "",
                          f"def {disk_name} : Rope (List Line) :=",
                          f"  {disk_tree}", "",
                          f"theorem {indexed_proof} :",
                          f"    Symbolic.IndexedRopeMatches "
                          f"{indices[0] * block_size} {wire_name} "
                          f"{indexed_name} := by",
                          f"  unfold {wire_name} {indexed_name}",
                          "  exact " + balanced(
                              [f"indexedWireLeafMatches{index:04d}"
                               for index in indices], ".leaf rfl"), "",
                          f"theorem {render_proof} :",
                          f"    {wire_name}.map "
                          "(fun wires => wires.map Wire.renderLine) = "
                          f"{disk_name} := by",
                          f"  unfold {wire_name} {disk_name}",
                          "  exact " + balanced_proof(
                              [f"renderWireBlock{index:04d}"
                               for index in indices]), ""]
        chunk_out += [f"end {namespace}", ""]
        write_if_changed(output.parent / f"TreeChunkBatch{batch_index:03d}.lean",
                         "\n".join(chunk_out))
    expected_tree_chunks = {
        f"TreeChunkBatch{i:03d}.lean" for i in range(len(tree_chunk_modules))}
    for stale in output.parent.glob("TreeChunkBatch*.lean"):
        if stale.name not in expected_tree_chunks:
            stale.unlink()
    for stale in output.parent.glob("RenderProof*.lean"):
        stale.unlink()

    # Keep the indexed semantic graph in a lightweight module.  Semantic
    # certificates should not pay to elaborate the disk-byte and complete
    # program data merely to resolve a wire index.
    indexed_out = prelude(["Loom.Release.SymbolicCertificate"] +
                          tree_chunk_modules,
                          namespace)
    indexed_out += ["def wireTree : Rope (List Wire) :=",
            "  " + balanced(wire_chunk_names, ".leaf []"), "",
            "def indexedWireTree : Rope (List Symbolic.IndexedWire) :=",
            "  " + balanced(indexed_chunk_names, ".leaf []"), "",
            *[
                f"theorem indexedWireResolveBlock{index:04d} (offset : Nat) :\n"
                "    indexedWireTree.resolve? "
                f"⟨[{', '.join('true' if step else 'false' for step in path)}], "
                f"offset⟩ = indexedWireBlock{index:04d}[offset]? := rfl\n"
                for index, path in enumerate(indexed_paths)
            ],
            "theorem indexedWiresMatch :",
            "    Symbolic.IndexedRopeMatches 0 wireTree indexedWireTree := by",
            "  unfold wireTree indexedWireTree",
            "  exact " + balanced(indexed_chunk_proofs, ".leaf rfl"), "",
            "def wireTable : Symbolic.WireTable where",
            f"  leafSize := {block_size}",
            f"  leafCount := {len(blocks)}", "",
            f"end {namespace}", ""]
    write_if_changed(indexed_root_path, "\n".join(indexed_out))
    emit_semantic_program(data, semantic_root_path, block_size,
                          indexed_root_module, namespace)

    program_modules = emit_batched_program(
        data, output, block_size, namespace, indexed_root_module,
        names, disk_names, proofs, disk_chunk_names, render_chunk_proofs)
    manifest = output.parent / "modules.txt"
    write_if_changed(manifest, "\n".join(
        batch_modules + indexed_batch_modules + tree_chunk_modules +
                        [indexed_root_module, semantic_root_module] +
                        program_modules +
                        [
                         root_module]) + "\n")

    if design_expr is not None:
        imports = design_imports or []
        # Do not clear generated certificate modules before regenerating them.
        # Every emitter below writes by content, so retaining identical files
        # preserves their mtimes and lets an interrupted kernel-check resume.
        # Known-size Python-generated families remove only surplus files after
        # their expected members have been written; synthesis-generated files
        # not imported by the current CertData module are inert.

        semantic_wire_modules = []
        semantic_wire_batch_size = 4
        semantic_wire_leaf_proofs = []
        for batch_index, start in enumerate(
                range(0, len(blocks), semantic_wire_batch_size)):
            module = f"{cert_module_prefix}.SemanticWireBatch{batch_index}"
            semantic_wire_modules.append(module)
            declarations = [
                "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                f"import {root_module}",
                "import Loom.Release.KernelDecide",
                "", f"namespace {namespace}", "", "open Loom.Release", "",
                "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""]
            for index in range(start, min(start + semantic_wire_batch_size,
                                          len(blocks))):
                block_proof = f"indexedWireSemanticBlock{index:04d}"
                leaf_proof = f"indexedWireSemanticLeaf{index:04d}"
                semantic_wire_leaf_proofs.append(leaf_proof)
                declarations += [f"theorem {block_proof} :",
                    "    Symbolic.indexedSemanticBlockMatches program indexedWireTree",
                    f"      wireTable {index * block_size} indexedWireBlock{index:04d} = true := kernel_decide", "",
                    f"theorem {leaf_proof} :",
                    "    Symbolic.IndexedRopeWellFormed program indexedWireTree wireTable",
                    f"      {index * block_size} (.leaf indexedWireBlock{index:04d}) :=",
                    f"  .leaf {block_proof}", ""]
            declarations += [f"end {namespace}", ""]
            write_if_changed(output.parent / f"SemanticWireBatch{batch_index}.lean",
                             "\n".join(declarations))

        expected_semantic_wires = {
            f"SemanticWireBatch{i}.lean"
            for i in range(len(semantic_wire_modules))}
        for stale in output.parent.glob("SemanticWireBatch*.lean"):
            if stale.name not in expected_semantic_wires:
                stale.unlink()

        semantic_wires = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT."] +
                          [f"import {module}" for module in semantic_wire_modules] +
                          ["", f"namespace {namespace}", "", "open Loom.Release", "",
                           "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
                           "theorem indexedWiresWellFormed :",
                           "    Symbolic.IndexedRopeWellFormed program indexedWireTree wireTable",
                           "      0 indexedWireTree := by",
                           "  unfold indexedWireTree",
                           "  exact " + balanced(semantic_wire_leaf_proofs,
                               ".leaf rfl"), "", f"end {namespace}", ""])
        write_if_changed(output.parent / "SemanticWires.lean",
                         "\n".join(semantic_wires))

        reg_batch_modules = []
        semantic_batch_size = 16
        for batch_index, start in enumerate(
                range(0, len(data["regs"]), semantic_batch_size)):
            module = f"{cert_module_prefix}.SemanticRegBatch{batch_index}"
            reg_batch_modules.append(module)
            indexed_batch_index = start // 16
            block = data["regs"][start:start + semantic_batch_size]
            if artifact == "Lnp64u":
                # The large release uses independently kernel-checked hybrid
                # action certificates.  Preserve the established batch-module
                # API as lightweight import wrappers so the downstream release
                # theorem does not need to change.
                declarations = [
                    "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                    *[
                        f"import {cert_module_prefix}.HybridReg{index:04d}"
                        for index in range(start, start + len(block))
                    ],
                    "",
                ]
                write_if_changed(
                    output.parent / f"SemanticRegBatch{batch_index}.lean",
                    "\n".join(declarations),
                )
                continue
            declarations = [
                "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                f"import {root_module}",
                *[f"import {design_import}" for design_import in imports],
                "import Loom.Release.KernelDecide",
                "import Loom.Release.SymbolicDecide",
                "import Loom.Release.SymbolicSound",
                "import Loom.Release.WholeRegisterPlan",
                f"import {cert_module_prefix}.PlanCertBatch{indexed_batch_index}",
                *[f"import {module}" for module in imports],
                "", f"namespace {namespace}", "", "open Loom.Release", "",
                "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""]
            source_name = f"wholePlanSources{batch_index}"
            entry_name = f"wholePlanEntries{batch_index}"
            aligned_name = f"wholePlanAligned{batch_index}"
            accepted_name = f"wholePlanAccepted{batch_index}"
            behaviors_name = f"wholePlanBehaviors{batch_index}"
            source_entries = [
                "  { name := " + q(reg["name"]) +
                f", width := {reg['width']}, init := BitVec.ofNat " +
                f"{reg['width']} {reg['init']} }}"
                for reg in block]
            plan_entries = [
                "  { root := " + root_ref(reg["next"]) +
                f", cert := wholePlanReleaseRegCert{index} }}"
                for index, reg in enumerate(block, start)]
            alignment = f".nil {start + len(block)}"
            for _ in reversed(block):
                alignment = f".cons rfl ({alignment})"
            declarations += [
                f"def {source_name} : List Loom.Hw.RegDecl := [",
                ",\n".join(source_entries), "]", "",
                f"def {entry_name} : List Symbolic.WholePlan.RegisterPlanRoot := [",
                ",\n".join(plan_entries), "]", "",
                f"theorem {aligned_name} :",
                f"    Symbolic.WholePlan.RegistersFrom ({design_expr}) {start}",
                f"      {source_name} :=",
                f"  {alignment}", "",
                f"theorem {accepted_name} :",
                f"    Symbolic.WholePlan.blockMatches ({design_expr}) program",
                f"      indexedWireTree wireTable {start}",
                f"      (Loom.Hw.Compile.RulePlans.ofRules {source_name}",
                f"        ({design_expr}).rules) {entry_name} = true := symbolic_kernel_decide", "",
                f"theorem {behaviors_name} :",
                f"    Symbolic.RegisterBehaviorsFrom ({design_expr}) program wireTable",
                f"      {start} (Symbolic.WholePlan.registerRootEntries {start} {entry_name}) := by",
                "  exact Symbolic.WholePlan.blockMatches_sound",
                f"    ({design_expr}) program indexedWiresMatch wireTable {start}",
                f"    {source_name}",
                f"    (Loom.Hw.Compile.RulePlans.ofRules {source_name} ({design_expr}).rules)",
                f"    {entry_name} {aligned_name}",
                f"    (Loom.Hw.Compile.RulePlans.ofRules_projects {source_name} ({design_expr}).rules)",
                f"    {accepted_name}", ""]
            tail_expr = behaviors_name
            for index in range(start, start + len(block)):
                root = root_ref(data["regs"][index]["next"])
                reg = data["regs"][index]
                declarations += [f"theorem semanticOutputBehavior{index} :",
                    f"    Symbolic.OutputBehaviorAt ({design_expr}) program {index} := by",
                    "  unfold Symbolic.OutputBehaviorAt",
                    "  exact ⟨rfl, rfl, rfl⟩", "",
                    f"theorem semanticRegisterBehavior{index} :",
                    f"    Symbolic.RegisterBehaviorAt ({design_expr}) program wireTable",
                    f"      {index} ({root}) := by",
                    "  exact Symbolic.WholePlan.RegisterBehaviorsFrom.head",
                    f"    ({tail_expr})", ""]
                tail_expr = ("Symbolic.WholePlan.RegisterBehaviorsFrom.tail " +
                             f"({tail_expr})")
            declarations += [f"end {namespace}", ""]
            write_if_changed(output.parent / f"SemanticRegBatch{batch_index}.lean",
                             "\n".join(declarations))

        expected_semantic_regs = {
            f"SemanticRegBatch{i}.lean"
            for i in range(len(reg_batch_modules))}
        for stale in output.parent.glob("SemanticRegBatch*.lean"):
            if stale.name not in expected_semantic_regs:
                stale.unlink()

        root_entries = [
            f"{{ index := {index}, root := {root_ref(reg['next'])} }}"
            for index, reg in enumerate(data["regs"])]
        root_block_decls = []
        root_block_names = []
        behavior_leaf_names = []
        output_block_names = []
        output_behavior_leaf_names = []
        register_block_size = 16
        for block_index, block in enumerate(chunks(list(enumerate(data["regs"])),
                                                   register_block_size)):
            block_name = f"registerRootBlock{block_index:04d}"
            leaf_name = f"registerBehaviorLeaf{block_index:04d}"
            root_block_names.append(f".leaf {block_name}")
            behavior_leaf_names.append(leaf_name)
            output_block_name = f"outputIndexBlock{block_index:04d}"
            output_leaf_name = f"outputBehaviorLeaf{block_index:04d}"
            output_block_names.append(f".leaf {output_block_name}")
            output_behavior_leaf_names.append(output_leaf_name)
            entries = [
                f"  {{ index := {index}, root := {root_ref(reg['next'])} }}"
                for index, reg in block]
            start_index = block[0][0] if block else 0
            proof = f".nil {start_index + len(block)}"
            for index, _ in reversed(block):
                proof = (f".cons rfl semanticRegisterBehavior{index} "
                         f"({proof})")
            output_proof = f".nil {start_index + len(block)}"
            for index, _ in reversed(block):
                output_proof = (f".cons rfl semanticOutputBehavior{index} "
                                f"({output_proof})")
            root_block_decls += [
                f"def {block_name} : List Symbolic.RegisterRoot := [",
                ",\n".join(entries), "]", "",
                f"theorem {leaf_name} :",
                "    Symbolic.RegisterBehaviorRopeFrom",
                f"      ({design_expr}) program wireTable {start_index}",
                f"      (.leaf {block_name}) :=",
                f"  .leaf ({proof})", "",
                f"def {output_block_name} : List Nat := [",
                "  " + ", ".join(str(index) for index, _ in block), "]", "",
                f"theorem {output_leaf_name} :",
                "    Symbolic.OutputBehaviorRopeFrom",
                f"      ({design_expr}) program {start_index}",
                f"      (.leaf {output_block_name}) :=",
                f"  .leaf ({output_proof})", ""]
        semantic_regs = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT."] +
                         [f"import {module}" for module in reg_batch_modules] +
                         ["", f"namespace {namespace}", "", "open Loom.Release", "",
                          "set_option maxRecDepth 1000000",
                          "set_option maxHeartbeats 0", ""] +
                         root_block_decls +
                         ["def registerRootTree : Rope (List Symbolic.RegisterRoot) :=",
                          "  " + balanced(root_block_names, ".leaf []"), "",
                          "theorem semanticRegisterBehaviors :",
                          "    Symbolic.RegisterBehaviorRopeFrom",
                          f"      ({design_expr}) program wireTable 0 registerRootTree := by",
                          "  unfold registerRootTree",
                          "  exact " + balanced(behavior_leaf_names, ".leaf (.nil 0)"), "",
                          "def outputIndexTree : Rope (List Nat) :=",
                          "  " + balanced(output_block_names, ".leaf []"), "",
                          "theorem semanticOutputBehaviors :",
                          "    Symbolic.OutputBehaviorRopeFrom",
                          f"      ({design_expr}) program 0 outputIndexTree := by",
                          "  unfold outputIndexTree",
                          "  exact " + balanced(output_behavior_leaf_names,
                              ".leaf (.nil 0)"), "",
                          "def registerRoots : List Symbolic.RegisterRoot := [",
                          "  " + ",\n  ".join(root_entries), "]", "",
                          f"end {namespace}", ""])
        write_if_changed(output.parent / "SemanticRegs.lean", "\n".join(semantic_regs))

        read_reg_modules = []
        for index, reg in enumerate(data["regs"]):
            module = f"{cert_module_prefix}.ReadRegBatch{index}"
            read_reg_modules.append(module)
            declarations = [
                "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                f"import {root_module}",
                *[f"import {design_import}" for design_import in imports],
                "import Loom.Release.KernelDecide",
                "import Loom.Release.SymbolicDecide",
                "", f"namespace {namespace}", "", "open Loom.Release", "",
                "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
                f"@[release_read_leaf] theorem semanticRegisterRead{index} :",
                "    Symbolic.HwExprRegistersValid program",
                f"      (.reg {reg['width']} {q(reg['name'])}) := by",
                "  exact Symbolic.hwExprRegistersValidB_sound _ kernel_decide", "",
                f"@[release_decl_leaf] theorem semanticRegisterDeclared{index} :",
                f"    Loom.Hw.Compile.registerDeclOk ({design_expr})",
                f"      {reg['width']} {q(reg['name'])} = true := kernel_decide", "",
                f"end {namespace}", ""]
            write_if_changed(output.parent / f"ReadRegBatch{index}.lean",
                             "\n".join(declarations))
        expected_read_regs = {
            f"ReadRegBatch{i}.lean" for i in range(len(read_reg_modules))}
        for stale in output.parent.glob("ReadRegBatch*.lean"):
            if stale.name not in expected_read_regs:
                stale.unlink()
        read_regs = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT."] +
                     [f"import {module}" for module in read_reg_modules] +
                     ["", f"namespace {namespace}", "", "open Loom.Release", "",
                      f"end {namespace}", ""])
        write_if_changed(output.parent / "ReadRegs.lean", "\n".join(read_regs))

        decl_mem_modules = []
        for index, memory in enumerate(data["mems"]):
            module = f"{cert_module_prefix}.DeclMemBatch{index}"
            decl_mem_modules.append(module)
            declarations = [
                "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                f"import {root_module}",
                *[f"import {design_import}" for design_import in imports],
                "import Loom.Release.KernelDecide",
                "import Loom.Release.SymbolicDecide",
                "", f"namespace {namespace}", "", "open Loom.Release", "",
                "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
                f"@[release_decl_leaf] theorem semanticMemoryDeclared{index} :",
                f"    Loom.Hw.Compile.memoryDeclOk ({design_expr})",
                f"      {memory['addrWidth']} {memory['dataWidth']} {q(memory['name'])} = true :=",
                "  kernel_decide", "", f"end {namespace}", ""]
            write_if_changed(output.parent / f"DeclMemBatch{index}.lean",
                             "\n".join(declarations))
        expected_decl_mems = {
            f"DeclMemBatch{i}.lean" for i in range(len(decl_mem_modules))}
        for stale in output.parent.glob("DeclMemBatch*.lean"):
            if stale.name not in expected_decl_mems:
                stale.unlink()
        decl_mems = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT."] +
                     [f"import {module}" for module in decl_mem_modules] +
                     ["", f"namespace {namespace}", "", "open Loom.Release", "",
                      f"end {namespace}", ""])
        write_if_changed(output.parent / "DeclMems.lean", "\n".join(decl_mems))

        semantic_actions = [
            "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
            f"import {cert_module_prefix}.ReadRegs",
            f"import {cert_module_prefix}.DeclMems",
            *[f"import {module}" for module in imports],
            "", f"namespace {namespace}", "", "open Loom.Release", "",
            "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
            "theorem semanticRulesDeclared :",
            f"    Loom.Hw.Compile.RulesDeclsOk ({design_expr}) ({design_expr}).rules :=",
            "  rules_decls_ok", "", f"end {namespace}", ""]
        write_if_changed(output.parent / "SemanticActions.lean",
                         "\n".join(semantic_actions))

        artifact = output.parent.name
        if artifact == "Lnp64u":
            semantic_design_wf = [
                "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                f"import {cert_module_prefix}.SemanticActions",
                "import Machines.Lnp64u.Theorems.ReleaseWF",
                "", f"namespace {namespace}", "",
                "open Loom.Hw.Compile", "",
                "theorem semanticDesignWellFormed :",
                f"    DesignWF ({design_expr}) :=",
                "  Machines.Lnp64u.Theorems.ReleaseWF.designWF_of_rules",
                "    Machines.Lnp64u.Demo.sysManifest semanticRulesDeclared", "",
                f"end {namespace}", ""]
            write_if_changed(output.parent / "SemanticDesignWF.lean",
                             "\n".join(semantic_design_wf))

        semantic_reads = [
            "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
            f"import {cert_module_prefix}.ReadRegs",
            *[f"import {module}" for module in imports],
            "", f"namespace {namespace}", "", "open Loom.Release", "",
            "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
            "theorem semanticDesignReads :",
            f"    Symbolic.DesignReadsValid ({design_expr}) program :=",
            "  design_reads_valid", "", f"end {namespace}", ""]
        write_if_changed(output.parent / "SemanticReads.lean",
                         "\n".join(semantic_reads))

        port_count = sum(len(memory["writes"]) for memory in data["mems"])
        port_cert_modules = [
            f"{cert_module_prefix}.IndexedPortCertBatch{index}"
            for index in range((port_count + 15) // 16)]

        def literal_ref(width: int, value: int) -> str:
            matches = [wire["name"] for wire in data["wires"]
                       if wire["width"] == width and
                       wire["rhs"] == f".lit {width} {value}"]
            if not matches:
                raise ValueError(f"missing literal {width}'d{value} in SSA witness")
            # ReleaseCertGen's expression index overwrites equal RHS keys, so
            # its chosen reference is the last occurrence in source order.
            return root_ref(matches[-1])

        semantic_mems = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                          f"import {root_module}",
                          "import Loom.Release.KernelDecide",
                          "import Loom.Release.SymbolicDecide",
                          "import Loom.Release.SymbolicSound",
                          *[f"import {module}" for module in port_cert_modules],
                          *[f"import {module}" for module in imports],
                          "", f"namespace {namespace}", "", "open Loom.Release", "",
                          "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""])
        memory_root_entries = []
        memory_behavior_names = []
        for memory_index, memory in enumerate(data["mems"]):
            source_name = f"sourceMemory{memory_index}"
            semantic_mems += [f"def {source_name} : Loom.Hw.MemDecl :=",
                f"  match ({design_expr}).mems[{memory_index}]? with",
                "  | some source => source",
                "  | none => { name := \"\", addrWidth := 0, dataWidth := 0,",
                "              init := fun _ => 0 }", "",
                f"theorem sourceMemory{memory_index}Found :",
                f"    ({design_expr}).mems[{memory_index}]? = some {source_name} := rfl", "",
                f"theorem concreteMemory{memory_index}Found :",
                f"    program.mems[{memory_index}]? = some mem{memory_index} := rfl", ""]
            init_behavior_names = []
            init_leaf_names = []
            for block_index, _ in enumerate(chunks(memory["init"], block_size)):
                start = block_index * block_size
                init_behavior = f"semanticMemory{memory_index}Init{block_index}Behavior"
                init_behavior_names.append(init_behavior)
                init_leaf_names.append(f".leaf mem{memory_index}Init{block_index:04d}")
                semantic_mems += [
                    f"theorem semanticMemory{memory_index}Init{block_index} :",
                    f"    (match ({design_expr}).mems[{memory_index}]? with",
                    f"      | some source => Symbolic.memoryInitBlockMatches source {start} " +
                    f"mem{memory_index}Init{block_index:04d}",
                    f"      | none => false) = true := kernel_decide", "",
                    f"theorem {init_behavior} :",
                    f"    match ({design_expr}).mems[{memory_index}]? with",
                    f"    | some source => Symbolic.MemoryInitBlockBehavior source {start}",
                    f"        mem{memory_index}Init{block_index:04d}",
                    "    | none => False :=",
                    "  Symbolic.memoryInitBlockBehaviorAt_of_check",
                    f"    ({design_expr}) {memory_index} {start}",
                    f"    mem{memory_index}Init{block_index:04d}",
                    f"    semanticMemory{memory_index}Init{block_index}", ""]
            init_tree = f"memoryInitTree{memory_index}"
            semantic_mems += [f"def {init_tree} : Rope (List Nat) :=",
                "  " + balanced(init_leaf_names, ".leaf []"), "",
                f"theorem semanticMemory{memory_index}InitBehavior :",
                f"    Symbolic.MemoryInitBehaviorAtRope ({design_expr})",
                f"      {memory_index} 0 {init_tree} := by",
                f"  unfold {init_tree}",
                "  exact " + balanced(
                    [f".leaf {name}" for name in init_behavior_names],
                    f".leaf semanticMemory{memory_index}Init0Behavior"), ""]
            port_at_names = []
            port_entries = []
            for port_index, write in enumerate(memory["writes"]):
                refs = ("{ en := " + root_ref(write["en"]) +
                        ", addr := " + root_ref(write["addr"]) +
                        ", data := " + root_ref(write["data"]) + " }")
                initial = ("{ en := " + literal_ref(1, 0) +
                           ", addr := " + literal_ref(memory["addrWidth"], 0) +
                           ", data := " + literal_ref(memory["dataWidth"], 0) + " }")
                prefix = f"semanticMemory{memory_index}Port{port_index}"
                port_at_names.append(f"{prefix}At")
                port_entries.append(
                    f"{{ index := {port_index}, refs := {refs} }}")
                semantic_mems += [f"theorem {prefix}Certificate :",
                    f"    Symbolic.nextPortRulesMatches indexedWireTree wireTable",
                    f"      {q(memory['name'])} {memory['addrWidth']} {memory['dataWidth']} {port_index}",
                    f"      ({design_expr}).rules ({initial}) ({refs})",
                    f"      indexedReleaseMem{memory_index}PortCert{port_index} = true := symbolic_kernel_decide", "",
                    f"theorem {prefix}InitialEn :",
                    "    Symbolic.indexedExprMatches indexedWireTree wireTable",
                    f"      (.lit (BitVec.ofNat 1 0)) ({literal_ref(1, 0)}) = true := symbolic_kernel_decide", "",
                    f"theorem {prefix}InitialAddr :",
                    "    Symbolic.indexedExprMatches indexedWireTree wireTable",
                    f"      (.lit (BitVec.ofNat {memory['addrWidth']} 0)) ({literal_ref(memory['addrWidth'], 0)}) = true := symbolic_kernel_decide", "",
                    f"theorem {prefix}InitialData :",
                    "    Symbolic.indexedExprMatches indexedWireTree wireTable",
                    f"      (.lit (BitVec.ofNat {memory['dataWidth']} 0)) ({literal_ref(memory['dataWidth'], 0)}) = true := symbolic_kernel_decide", "",
                    f"theorem {prefix}Behavior :",
                    f"    Symbolic.MemoryPortBehavior ({design_expr}) program wireTable",
                    f"      {q(memory['name'])} {memory['addrWidth']} {memory['dataWidth']} {port_index} ({refs}) := by",
                    "  exact Symbolic.memoryPortBehavior_of_checks",
                    f"    ({design_expr}) program indexedWiresMatch wireTable",
                    f"    {q(memory['name'])} {memory['addrWidth']} {memory['dataWidth']} {port_index}",
                    f"    ({initial}) ({refs}) indexedReleaseMem{memory_index}PortCert{port_index}",
                    f"    {prefix}Certificate {prefix}InitialEn",
                    f"    {prefix}InitialAddr {prefix}InitialData", "",
                    f"theorem {prefix}At :",
                    f"    Symbolic.MemoryPortBehaviorAt ({design_expr}) program wireTable",
                    f"      {memory_index} {port_index} ({refs}) := by",
                    "  apply Symbolic.memoryPortBehaviorAt_of_checks",
                    f"    ({design_expr}) program wireTable {memory_index} {port_index}",
                    f"    {source_name} mem{memory_index}",
                    f"    ({{ en := {q(write['en'])}, addr := {q(write['addr'])},",
                    f"       data := {q(write['data'])} }} : Loom.Release.SSA.Write)",
                    f"    ({refs}) sourceMemory{memory_index}Found",
                    f"    concreteMemory{memory_index}Found rfl rfl rfl rfl rfl rfl rfl",
                    f"  simpa [{source_name}] using {prefix}Behavior", ""]
            port_roots = f"memoryPortRoots{memory_index}"
            port_proof = f".nil {len(port_entries)}"
            for port_index, proof_name in reversed(list(enumerate(port_at_names))):
                port_proof = f".cons rfl {proof_name} ({port_proof})"
            semantic_mems += [f"def {port_roots} : List Symbolic.MemoryPortRoot := [",
                "  " + ",\n  ".join(port_entries), "]", "",
                f"theorem semanticMemory{memory_index}PortBehaviors :",
                "    Symbolic.MemoryPortBehaviorsFrom",
                f"      ({design_expr}) program wireTable {memory_index} 0 {port_roots} :=",
                f"  {port_proof}", "",
                f"theorem semanticMemory{memory_index}Behavior :",
                f"    Symbolic.MemoryBehaviorAt ({design_expr}) program wireTable",
                f"      {memory_index} {init_tree} {port_roots} := by",
                "  apply Symbolic.memoryBehaviorAt_of_checks",
                f"    ({design_expr}) program wireTable {memory_index}",
                f"    {source_name} mem{memory_index} {init_tree} {port_roots}",
                f"    sourceMemory{memory_index}Found concreteMemory{memory_index}Found",
                f"    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)",
                f"    semanticMemory{memory_index}InitBehavior",
                f"    semanticMemory{memory_index}PortBehaviors", ""]
            memory_root_entries.append(
                f"{{ index := {memory_index}, init := {init_tree}, ports := {port_roots} }}")
            memory_behavior_names.append(f"semanticMemory{memory_index}Behavior")
        memory_proof = f".nil {len(memory_root_entries)}"
        for memory_index, behavior_name in reversed(
                list(enumerate(memory_behavior_names))):
            memory_proof = f".cons rfl {behavior_name} ({memory_proof})"
        semantic_mems += ["def memoryRoots : List Symbolic.MemoryRoot := [",
            "  " + ",\n  ".join(memory_root_entries), "]", "",
            "theorem semanticMemoryBehaviors :",
            "    Symbolic.MemoryBehaviorsFrom",
            f"      ({design_expr}) program wireTable 0 memoryRoots :=",
            f"  {memory_proof}", ""]
        semantic_mems += [f"end {namespace}", ""]
        write_if_changed(output.parent / "SemanticMems.lean", "\n".join(semantic_mems))

        semantic_module = [
            "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
            "import Loom.Release.KernelDecide",
            f"import {cert_module_prefix}.SemanticWires",
            f"import {cert_module_prefix}.SemanticRegs",
            f"import {cert_module_prefix}.SemanticMems",
            f"import {cert_module_prefix}.SemanticReads",
            "", f"namespace {namespace}", "", "open Loom.Release", "",
            "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", "",
            "theorem semanticModuleBehavior :",
            f"    Symbolic.ModuleBehavior ({design_expr}) program indexedWireTree",
            "      wireTable registerRootTree memoryRoots outputIndexTree := by",
            "  exact Symbolic.moduleBehavior_of_checks",
            f"    ({design_expr}) program indexedWireTree wireTable",
            "    registerRootTree memoryRoots outputIndexTree",
            "    (by rfl) indexedWiresMatch indexedWiresWellFormed",
            "    semanticDesignReads kernel_decide kernel_decide",
            "    kernel_decide kernel_decide kernel_decide",
            "    semanticRegisterBehaviors semanticMemoryBehaviors",
            "    semanticOutputBehaviors", "", f"end {namespace}", ""]
        write_if_changed(output.parent / "SemanticModule.lean",
                         "\n".join(semantic_module))

        if artifact == "Acc8":
            spec_expr = ("Machines.Acc8.machine "
                         "(Machines.Acc8.loadProg Machines.Acc8.golden)")
            semantic_release = [
                "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                f"import {cert_module_prefix}.SemanticModule",
                "import Loom.Release.SymbolicVerified",
                "import Machines.Acc8.Theorems.AR",
                "import Machines.Acc8.Theorems.AEV",
                "", f"namespace {namespace}", "",
                "open Loom Loom.Release Loom.Hw", "",
                "theorem semanticProcessorRefinement :",
                f"    Nonempty (Simulation ({spec_expr})",
                f"      (Compile.compile ({design_expr})).toTSys.reachablePart) := by",
                "  obtain ⟨source⟩ := Machines.Acc8.Theorems.AR.refines",
                "    (Machines.Acc8.loadProg Machines.Acc8.golden)",
                "  obtain ⟨compiler⟩ := Machines.Acc8.Theorems.AEV.emission_correct",
                "    (Machines.Acc8.loadProg Machines.Acc8.golden)",
                "  exact ⟨(source.comp compiler).concreteReachablePart⟩", "",
                "theorem verifiedRelease :",
                "    Nonempty (VerifiedSymbolicArtifact",
                f"      ({spec_expr}) ({design_expr}) program diskTree",
                "      indexedWireTree wireTable registerRootTree memoryRoots",
                "      outputIndexTree) := by",
                "  obtain ⟨refinement⟩ := semanticProcessorRefinement",
                "  exact verifiedSymbolicArtifact_of_checks",
                f"    ({spec_expr}) ({design_expr}) program diskTree",
                "    indexedWireTree wireTable registerRootTree memoryRoots",
                "    outputIndexTree exactBytes semanticModuleBehavior",
                "    refinement", "", f"end {namespace}", ""]
            write_if_changed(output.parent / "SemanticRelease.lean",
                             "\n".join(semantic_release))
        elif artifact == "Lnp64u":
            spec_expr = "Machines.Lnp64u.machine Machines.Lnp64u.Demo.sysManifest"
            semantic_release = [
                "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                f"import {cert_module_prefix}.SemanticModule",
                f"import {cert_module_prefix}.SemanticDesignWF",
                "import Loom.Release.SymbolicVerified",
                "import Machines.Lnp64u.Theorems.DemoWitness",
                "import Machines.Lnp64u.Theorems.RMC",
                "", f"namespace {namespace}", "",
                "open Loom Loom.Release Loom.Hw", "",
                "theorem semanticProcessorRefinement :",
                f"    Nonempty (Simulation ({spec_expr})",
                f"      (Compile.compile ({design_expr})).toTSys.reachablePart) := by",
                "  obtain ⟨source⟩ := Machines.Lnp64u.Theorems.RMC.refines",
                "    Machines.Lnp64u.Demo.sysManifest",
                "    Machines.Lnp64u.Theorems.DemoWitness.sys_wf",
                "    Machines.Lnp64u.Theorems.DemoWitness.sys_fits",
                "  let orbit : Simulation",
                "      (Machines.Lnp64u.Theorems.RMC.reachCore",
                "        Machines.Lnp64u.Demo.sysManifest)",
                f"      ({design_expr}).toTSys.reachablePart :=",
                "    { abs := id",
                "      init_ok := fun _ initial => initial",
                "      square := fun _ _ step => step }",
                "  let compiler := Compile.simulation",
                f"    ({design_expr}) semanticDesignWellFormed",
                "  exact ⟨(source.comp orbit).comp compiler.reachablePart⟩", "",
                "theorem verifiedRelease :",
                "    Nonempty (VerifiedSymbolicArtifact",
                f"      ({spec_expr}) ({design_expr}) program diskTree",
                "      indexedWireTree wireTable registerRootTree memoryRoots",
                "      outputIndexTree) := by",
                "  obtain ⟨refinement⟩ := semanticProcessorRefinement",
                "  exact verifiedSymbolicArtifact_of_checks",
                f"    ({spec_expr}) ({design_expr}) program diskTree",
                "    indexedWireTree wireTable registerRootTree memoryRoots",
                "    outputIndexTree exactBytes semanticModuleBehavior",
                "    refinement", "", f"end {namespace}", ""]
            write_if_changed(output.parent / "SemanticRelease.lean",
                             "\n".join(semantic_release))

        cert_data = output.parent / "CertData.lean"
        cert_prefix = (f"import {root_module}\n" +
                       "import Loom.Release.NamedCertificate\n" +
                       "".join(f"import {module}\n" for module in imports) +
                       f"namespace {namespace}\nopen Loom.Release\n" +
                       "set_option maxRecDepth 1000000\n" +
                       "set_option maxHeartbeats 0\n" +
                       "set_option linter.unusedTactic false\n" +
                       f"def design := {design_expr}\n")
        cert_body = ("\ndef cert : Named.ModuleCert design := ")
        cert_suffix = ("\n" +
                       "theorem accepted : ssaNamedMatches design program cert = true := " +
                       "kernel_decide\n" +
                       f"end {namespace}\n")
        cert_gen = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT."] +
                    [f"import {module}" for module in
                     ["Tools.ReleaseCertGen"] + imports] +
                    ["", "private def writeIfChanged (path contents : String) : IO Unit := do",
                     "  try",
                     "    if (← IO.FS.readFile path) == contents then return",
                     "  catch _ => pure ()",
                     "  IO.FS.writeFile path contents",
                     "", "unsafe def main : IO Unit := do",
                     f"  let design := {design_expr}",
                     f"  let program ← Tools.RuntimeSsa.load "
                       f"{q(str(output.parent / 'Runtime.tsv'))}",
                     "  let some (cert, planCerts) := " +
                       "Tools.ReleaseCertGen."
                       "synthesizeWithPlanRegisterCertsRuntime design program",
                     "    | throw (IO.userError \"certificate synthesis failed\")",
                     "  let batches := Tools.ReleaseCertGen.declarationBatchesToLean cert 16",
                     "  for (body, index) in batches.zipIdx do",
                     f"    writeIfChanged (s!\"{output.parent}/CertBatch{{index}}.lean\") <|",
                     f"      {q('import Loom.Release.NamedCertificate\nnamespace ' + namespace + '\nopen Loom.Release\nset_option maxRecDepth 1000000\n')} ++",
                     f"      body ++ {q('end ' + namespace + '\n')}",
                     "  let indexedBatches := Tools.ReleaseCertGen.indexedDeclarationBatchesToLean cert 16",
                     "  for (body, index) in indexedBatches.zipIdx do",
                     f"    writeIfChanged (s!\"{output.parent}/IndexedCertBatch{{index}}.lean\") <|",
                     f"      {q('import Loom.Release.SymbolicCertificate\nnamespace ' + namespace + '\nopen Loom.Release\nset_option maxRecDepth 1000000\n')} ++",
                     f"      body ++ {q('end ' + namespace + '\n')}",
                     "  let planBatches := Tools.ReleaseCertGen.planDeclarationBatchesToLean planCerts 16",
                     "  for (body, index) in planBatches.zipIdx do",
                     f"    writeIfChanged (s!\"{output.parent}/PlanCertBatch{{index}}.lean\") <|",
                     f"      {q('import Loom.Release.WholeRegisterPlan\nnamespace ' + namespace + '\nopen Loom.Release\nset_option maxRecDepth 1000000\n')} ++",
                     f"      body ++ {q('end ' + namespace + '\n')}",
                     "  let indexedPortBatches := Tools.ReleaseCertGen.indexedPortDeclarationBatchesToLean cert 16",
                     "  for (body, index) in indexedPortBatches.zipIdx do",
                     f"    writeIfChanged (s!\"{output.parent}/IndexedPortCertBatch{{index}}.lean\") <|",
                     f"      {q('import Loom.Release.SymbolicCertificate\nnamespace ' + namespace + '\nopen Loom.Release\nset_option maxRecDepth 1000000\n')} ++",
                     f"      body ++ {q('end ' + namespace + '\n')}",
                     "  let batchImports := String.join <| batches.zipIdx.map fun (_, index) =>",
                     f"    s!\"import {cert_module_prefix}.CertBatch{{index}}\\n\"",
                     f"  writeIfChanged {q(str(cert_data))} <|",
                     f"    batchImports ++ {q(cert_prefix)} ++",
                     f"      {q(cert_body)} ++ Tools.ReleaseCertGen.toLean cert ++",
                     f"      {q(cert_suffix)}", ""])
        write_if_changed(output.parent / "CertGen.lean", "\n".join(cert_gen))

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--block-size", type=int, default=512)
    parser.add_argument("--batch-blocks", type=int, default=0,
                        help="write this many leaves per imported batch module")
    parser.add_argument("--design-expr",
                        help="Lean design expression for certificate generation")
    parser.add_argument("--design-import", action="append", default=[],
                        help="module imported by the generated certificate driver")
    args = parser.parse_args()
    data = parse(args.input)
    runtime_lines = [f"LOOM_SSA_V1\t{data['name']}"]
    runtime_lines += ["\t".join(("R", reg["name"], str(reg["width"]),
                                 str(reg["init"]), reg["next"]))
                      for reg in data["regs"]]
    runtime_wires = []
    for wire in data["wires"]:
        compact = wire["runtimeRhs"]
        runtime_wires.append("\t".join((
            "W", wire["name"], str(wire["width"]), compact["op"],
            ",".join(compact["strings"]),
            ",".join(str(value) for value in compact["nums"]))))
    runtime_lines += [";".join(block) for block in chunks(runtime_wires, 32)]
    write_if_changed(args.output.parent / "Runtime.tsv",
                     "\n".join(runtime_lines) + "\n")
    if args.batch_blocks:
        emit_batched(data, args.output, args.block_size, args.batch_blocks,
                     args.design_expr, args.design_import)
    else:
        emit(data, args.output, args.block_size)


if __name__ == "__main__":
    main()
