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
    return f".wire {match[1]}" if match else f".reg {q(name)}"


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
        indexed_name = f"indexedWireBlock{index:04d}"
        indexed_entries = [
            f"  {{ number := {index * block_size + offset}, "
            f"width := {w['width']}, rhs := {w['indexedRhs']} }}"
            for offset, w in enumerate(block)]
        out += [f"def {indexed_name} : List Symbolic.IndexedWire := [",
                ",\n".join(indexed_entries), "]", "",
                f"theorem indexedWireBlockMatches{index:04d} :",
                f"    Symbolic.indexedBlockMatches {index * block_size} " +
                  f"{name} {indexed_name} = true := rfl", ""]
        out += [f"theorem indexedWireLeafMatches{index:04d} :",
                f"    Symbolic.IndexedRopeMatches {index * block_size} " +
                  f"(.leaf {name}) (.leaf {indexed_name}) :=",
                f"  .leaf indexedWireBlockMatches{index:04d}", ""]
        disk_entries = ",\n".join(f"  {q(w['line'])}" for w in block)
        out += [f"def {disk_name} : List String := [", disk_entries, "]", "",
                f"theorem {proof_name} :",
                f"    {name}.map Wire.render = {disk_name} := rfl", ""]
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
                      "indexedRhs": indexed_rhs(match[3]), "line": lines[i]})
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

    names = [f"wireBlock{i:04d}" for i in range(len(blocks))]
    indexed_names = [f"indexedWireBlock{i:04d}" for i in range(len(blocks))]
    disk_names = [f"diskWireBlock{i:04d}" for i in range(len(blocks))]
    proofs = [f"renderWireBlock{i:04d}" for i in range(len(blocks))]
    indexed_proofs = [f"indexedWireLeafMatches{i:04d}" for i in range(len(blocks))]
    out = prelude(["Loom.Release.Certificate",
                   "Loom.Release.SymbolicCertificate"] + batch_modules,
                  namespace)
    out += ["def wireTree : Rope (List Wire) :=",
            "  " + balanced(names, ".leaf []").replace(
                "wireBlock", ".leaf wireBlock"), "",
            "def indexedWireTree : Rope (List Symbolic.IndexedWire) :=",
            "  " + balanced(indexed_names, ".leaf []").replace(
                "indexedWireBlock", ".leaf indexedWireBlock"), "",
            "theorem indexedWiresMatch :",
            "    Symbolic.IndexedRopeMatches 0 wireTree indexedWireTree := by",
            "  unfold wireTree indexedWireTree",
            "  exact " + balanced(indexed_proofs, ".leaf rfl").replace(
                ".node", ".node"), "",
            "def wireTable : Symbolic.WireTable where",
            f"  leafSize := {block_size}",
            "  paths := [" + ", ".join(
                "[" + ", ".join("true" if step else "false" for step in path) + "]"
                for path in balanced_paths(len(blocks))) + "]", "",
            "def diskWireTree : Rope (List String) :=",
            "  " + balanced(disk_names, ".leaf []").replace(
                "diskWireBlock", ".leaf diskWireBlock"), "",
            "theorem renderWireTree :",
            "    wireTree.map (fun wires => wires.map Wire.render) = diskWireTree := by",
            "  unfold wireTree diskWireTree",
            "  exact " + balanced_proof(proofs), ""]
    emit_program_tail(out, data, block_size, namespace)
    write_if_changed(output, "\n".join(out))
    manifest = output.parent / "modules.txt"
    write_if_changed(manifest, "\n".join(batch_modules + [root_module]) + "\n")

    if design_expr is not None:
        imports = design_imports or []
        for stale in output.parent.glob("CertBatch*.lean"):
            stale.unlink()
        for stale in output.parent.glob("SemanticRegBatch*.lean"):
            stale.unlink()
        for stale in output.parent.glob("SemanticWireBatch*.lean"):
            stale.unlink()
        for stale in output.parent.glob("IndexedPortCertBatch*.lean"):
            stale.unlink()

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
        semantic_batch_size = 1
        for batch_index, start in enumerate(
                range(0, len(data["regs"]), semantic_batch_size)):
            module = f"{cert_module_prefix}.SemanticRegBatch{batch_index}"
            reg_batch_modules.append(module)
            indexed_batch_index = start // 16
            declarations = [
                "-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                f"import {root_module}",
                *[f"import {design_import}" for design_import in imports],
                "import Loom.Release.KernelDecide",
                "import Loom.Release.SymbolicDecide",
                "import Loom.Release.SymbolicSound",
                f"import {cert_module_prefix}.IndexedCertBatch{indexed_batch_index}",
                *[f"import {module}" for module in imports],
                "", f"namespace {namespace}", "", "open Loom.Release", "",
                "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""]
            for index in range(start, min(start + semantic_batch_size,
                                          len(data["regs"]))):
                root = indexed_ref(data["regs"][index]["next"])
                reg = data["regs"][index]
                declarations += [f"theorem semanticRegisterMetadata{index} :",
                    f"    Symbolic.indexedRegisterMetadataMatchesAt ({design_expr}) program",
                    f"      {index} ({root}) = true := rfl", "",
                    f"theorem semanticRegister{index} :",
                    f"    Symbolic.nextRulesMatches indexedWireTree wireTable",
                    f"      {q(reg['name'])} {reg['width']} ({design_expr}).rules",
                    f"      (some (.reg {q(reg['name'])})) ({root}) indexedReleaseRegCert{index} = true := symbolic_kernel_decide", "",
                    f"theorem semanticRegisterBehavior{index} :",
                    f"    Symbolic.RegisterBehaviorAt ({design_expr}) program wireTable",
                    f"      {index} ({root}) := by",
                    "  exact Symbolic.registerBehaviorAt_of_checks",
                    f"    ({design_expr}) program indexedWiresMatch wireTable {index}",
                    f"    ({{ name := {q(reg['name'])}, width := {reg['width']},",
                    f"       init := BitVec.ofNat {reg['width']} {reg['init']} }} : Loom.Hw.RegDecl)",
                    f"    ({root}) indexedReleaseRegCert{index} rfl",
                    f"    semanticRegisterMetadata{index} semanticRegister{index}", ""]
            declarations += [f"end {namespace}", ""]
            write_if_changed(output.parent / f"SemanticRegBatch{batch_index}.lean",
                             "\n".join(declarations))

        root_entries = [
            f"{{ index := {index}, root := {indexed_ref(reg['next'])} }}"
            for index, reg in enumerate(data["regs"])]
        root_block_decls = []
        root_block_names = []
        behavior_leaf_names = []
        register_block_size = 16
        for block_index, block in enumerate(chunks(list(enumerate(data["regs"])),
                                                   register_block_size)):
            block_name = f"registerRootBlock{block_index:04d}"
            leaf_name = f"registerBehaviorLeaf{block_index:04d}"
            root_block_names.append(f".leaf {block_name}")
            behavior_leaf_names.append(leaf_name)
            entries = [
                f"  {{ index := {index}, root := {indexed_ref(reg['next'])} }}"
                for index, reg in block]
            start_index = block[0][0] if block else 0
            proof = f".nil {start_index + len(block)}"
            for index, _ in reversed(block):
                proof = (f".cons rfl semanticRegisterBehavior{index} "
                         f"({proof})")
            root_block_decls += [
                f"def {block_name} : List Symbolic.RegisterRoot := [",
                ",\n".join(entries), "]", "",
                f"theorem {leaf_name} :",
                "    Symbolic.RegisterBehaviorRopeFrom",
                f"      ({design_expr}) program wireTable {start_index}",
                f"      (.leaf {block_name}) :=",
                f"  .leaf ({proof})", ""]
        semantic_regs = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT."] +
                         [f"import {module}" for module in reg_batch_modules] +
                         ["", f"namespace {namespace}", "", "open Loom.Release", ""] +
                         root_block_decls +
                         ["def registerRootTree : Rope (List Symbolic.RegisterRoot) :=",
                          "  " + balanced(root_block_names, ".leaf []"), "",
                          "theorem semanticRegisterBehaviors :",
                          "    Symbolic.RegisterBehaviorRopeFrom",
                          f"      ({design_expr}) program wireTable 0 registerRootTree := by",
                          "  unfold registerRootTree",
                          "  exact " + balanced(behavior_leaf_names, ".leaf (.nil 0)"), "",
                          "def registerRoots : List Symbolic.RegisterRoot := [",
                          "  " + ",\n  ".join(root_entries), "]", "",
                          f"end {namespace}", ""])
        write_if_changed(output.parent / "SemanticRegs.lean", "\n".join(semantic_regs))

        for stale in output.parent.glob("ReadRegBatch*.lean"):
            stale.unlink()
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
        read_regs = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT."] +
                     [f"import {module}" for module in read_reg_modules] +
                     ["", f"namespace {namespace}", "", "open Loom.Release", "",
                      f"end {namespace}", ""])
        write_if_changed(output.parent / "ReadRegs.lean", "\n".join(read_regs))

        for stale in output.parent.glob("DeclMemBatch*.lean"):
            stale.unlink()
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
            return indexed_ref(matches[-1])

        semantic_mems = (["-- Generated by scripts/gen_release_witness.py; DO NOT EDIT.",
                          f"import {root_module}",
                          "import Loom.Release.KernelDecide",
                          "import Loom.Release.SymbolicDecide",
                          "import Loom.Release.SymbolicSound",
                          *[f"import {module}" for module in port_cert_modules],
                          *[f"import {module}" for module in imports],
                          "", f"namespace {namespace}", "", "open Loom.Release", "",
                          "set_option maxRecDepth 1000000", "set_option maxHeartbeats 0", ""])
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
                refs = ("{ en := " + indexed_ref(write["en"]) +
                        ", addr := " + indexed_ref(write["addr"]) +
                        ", data := " + indexed_ref(write["data"]) + " }")
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
        semantic_mems += [f"end {namespace}", ""]
        write_if_changed(output.parent / "SemanticMems.lean", "\n".join(semantic_mems))

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
                     [root_module, "Tools.ReleaseCertGen"] + imports] +
                    ["", "unsafe def main : IO Unit := do",
                     f"  let design := {design_expr}",
                     "  let some cert := Tools.ReleaseCertGen.synthesize design " +
                       f"{namespace}.program",
                     "    | throw (IO.userError \"certificate synthesis failed\")",
                     "  let batches := Tools.ReleaseCertGen.declarationBatchesToLean cert 16",
                     "  for (body, index) in batches.zipIdx do",
                     f"    IO.FS.writeFile (s!\"{output.parent}/CertBatch{{index}}.lean\") <|",
                     f"      {q('import Loom.Release.NamedCertificate\nnamespace ' + namespace + '\nopen Loom.Release\nset_option maxRecDepth 1000000\n')} ++",
                     f"      body ++ {q('end ' + namespace + '\n')}",
                     "  let indexedBatches := Tools.ReleaseCertGen.indexedDeclarationBatchesToLean cert 16",
                     "  for (body, index) in indexedBatches.zipIdx do",
                     f"    IO.FS.writeFile (s!\"{output.parent}/IndexedCertBatch{{index}}.lean\") <|",
                     f"      {q('import Loom.Release.SymbolicCertificate\nnamespace ' + namespace + '\nopen Loom.Release\nset_option maxRecDepth 1000000\n')} ++",
                     f"      body ++ {q('end ' + namespace + '\n')}",
                     "  let indexedPortBatches := Tools.ReleaseCertGen.indexedPortDeclarationBatchesToLean cert 16",
                     "  for (body, index) in indexedPortBatches.zipIdx do",
                     f"    IO.FS.writeFile (s!\"{output.parent}/IndexedPortCertBatch{{index}}.lean\") <|",
                     f"      {q('import Loom.Release.SymbolicCertificate\nnamespace ' + namespace + '\nopen Loom.Release\nset_option maxRecDepth 1000000\n')} ++",
                     f"      body ++ {q('end ' + namespace + '\n')}",
                     "  let batchImports := String.join <| batches.zipIdx.map fun (_, index) =>",
                     f"    s!\"import {cert_module_prefix}.CertBatch{{index}}\\n\"",
                     f"  IO.FS.writeFile {q(str(cert_data))} <|",
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
    if args.batch_blocks:
        emit_batched(data, args.output, args.block_size, args.batch_blocks,
                     args.design_expr, args.design_import)
    else:
        emit(data, args.output, args.block_size)


if __name__ == "__main__":
    main()
