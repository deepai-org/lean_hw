#!/usr/bin/env python3
"""Exact byte binding between generated Lean disk leaves and shipped RTL.

This intentionally tiny checker is the release pipeline's one external byte
comparison. It reads the literal `disk*` list declarations that occur in the
kernel-checked proof modules, reconstructs their theorem-defined order, and
compares the resulting UTF-8 bytes exactly with the `.v` file.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path


START = re.compile(r"^def (disk\w+) : List String := \[$")
INLINE = re.compile(r"^def (disk\w+) : List String := \[(.*)\]$")
FRAGMENT_START = re.compile(r"^def (diskWireBlock\d+) : List Line := \[$")
FRAGMENT_ENTRY = re.compile(r"^\{ fragments := \[(.*)\] \},?$")
ROPE_DEF = re.compile(
    r"^def (\w+) : Rope \(List (?:String|Line)\) :=\n(.*?)(?=\n\n)",
    re.MULTILINE | re.DOTALL)
LIST_DEF = re.compile(
    r"^def (\w+) : List String :=\n(.*?)(?=\n\n)",
    re.MULTILINE | re.DOTALL)
_DEFINITION_CACHE: dict[Path, tuple[dict[str, str], dict[str, str]]] = {}


def definition_index(directory: Path) -> tuple[dict[str, str], dict[str, str]]:
    key = directory.resolve()
    if key in _DEFINITION_CACHE:
        return _DEFINITION_CACHE[key]
    ropes: dict[str, str] = {}
    lists: dict[str, str] = {}
    for source in sorted(directory.glob("*.lean")):
        text = source.read_text()
        for match in ROPE_DEF.finditer(text):
            if match[1] in ropes:
                raise ValueError(f"duplicate rope definition {match[1]}")
            ropes[match[1]] = match[2].strip()
        for match in LIST_DEF.finditer(text):
            if match[1] in lists:
                raise ValueError(f"duplicate list definition {match[1]}")
            lists[match[1]] = match[2].strip()
    _DEFINITION_CACHE[key] = (ropes, lists)
    return ropes, lists


def declarations(directory: Path) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for source in sorted(directory.glob("*.lean")):
        lines = source.read_text().splitlines()
        i = 0
        while i < len(lines):
            fragment_start = FRAGMENT_START.fullmatch(lines[i])
            if fragment_start:
                values: list[str] = []
                i += 1
                while i < len(lines) and lines[i] != "]":
                    entry = FRAGMENT_ENTRY.fullmatch(lines[i].strip())
                    if not entry:
                        raise ValueError(f"bad fragment line: {lines[i]}")
                    fragments = json.loads("[" + entry[1] + "]")
                    values.append("".join(fragments))
                    i += 1
                if i == len(lines):
                    raise ValueError(f"unterminated disk declaration {fragment_start[1]}")
                result[fragment_start[1]] = values
                i += 1
                continue
            inline = INLINE.fullmatch(lines[i])
            if inline:
                values = [] if not inline[2] else [json.loads(inline[2])]
                if inline[1] in result:
                    raise ValueError(f"duplicate disk declaration {inline[1]}")
                result[inline[1]] = values
                i += 1
                continue
            start = START.fullmatch(lines[i])
            if not start:
                i += 1
                continue
            values: list[str] = []
            i += 1
            while i < len(lines) and lines[i] != "]":
                text = lines[i].strip()
                if text.endswith(","):
                    text = text[:-1]
                values.append(json.loads(text))
                i += 1
            if i == len(lines):
                raise ValueError(f"unterminated disk declaration {start[1]}")
            if start[1] in result:
                raise ValueError(f"duplicate disk declaration {start[1]}")
            result[start[1]] = values
            i += 1
    return result


def rope_definition(directory: Path, name: str) -> str:
    ropes, _ = definition_index(directory)
    if name not in ropes:
        raise ValueError(f"missing rope definition {name}")
    expression = ropes[name]
    if not re.fullmatch(r"[.()A-Za-z0-9_\s]+", expression):
        raise ValueError(f"unexpected syntax in rope definition {name}")
    return expression


def rope_references(expression: str, allowed: re.Pattern[str]) -> list[str]:
    identifiers = re.findall(r"[A-Za-z_]\w*", expression)
    references = [name for name in identifiers if name not in ("node", "leaf")]
    unexpected = [name for name in references if not allowed.fullmatch(name)]
    if unexpected:
        raise ValueError(f"unexpected rope references: {', '.join(unexpected)}")
    return references


def list_concat_references(directory: Path, name: str,
                           allowed: re.Pattern[str]) -> list[str]:
    _, lists = definition_index(directory)
    if name not in lists:
        raise ValueError(f"expected one concatenated list definition {name}")
    expression = lists[name]
    # Parentheses are permitted so generated append trees can be balanced;
    # references are still recovered and checked in exact lexical/source order.
    if not re.fullmatch(r"[+()A-Za-z0-9_\s]+", expression):
        raise ValueError(f"unexpected syntax in list definition {name}")
    references = re.findall(r"[A-Za-z_]\w*", expression)
    unexpected = [reference for reference in references
                  if not allowed.fullmatch(reference)]
    if unexpected:
        raise ValueError(f"unexpected list references: {', '.join(unexpected)}")
    return references


def ordered_names(directory: Path, values: dict[str, list[str]]) -> list[str]:
    """Derive the byte order from the exact rope used by Lean's theorem."""
    root = (directory / "Root.lean").read_text()
    top = " ".join(rope_definition(directory, "diskTree").split())
    expected_top = (".node (.leaf diskPrefix) "
                    "(.node diskMemTrees (.node diskWireTree (.leaf diskSuffix)))")
    if top != expected_top:
        raise ValueError("diskTree is not the fixed release framing")

    memory_trees = rope_references(
        rope_definition(directory, "diskMemTrees"),
        re.compile(r"diskMem\d+Tree"))
    memory_numbers = [int(re.fullmatch(r"diskMem(\d+)Tree", name)[1])
                      for name in memory_trees]
    if memory_numbers != list(range(len(memory_numbers))):
        raise ValueError("memory trees are not in contiguous source order")

    prefix_refs = list_concat_references(
        directory, "diskPrefix",
        re.compile(r"disk(?:Header|RegDeclBlock\d{4}|MemDecls)"))
    expected_prefix = (["diskHeader"] + sorted(
        name for name in values if re.fullmatch(r"diskRegDeclBlock\d{4}", name)) +
        ["diskMemDecls"])
    if prefix_refs != expected_prefix:
        raise ValueError("prefix leaves are not in source order")
    names = prefix_refs
    for number in memory_numbers:
        tree_name = f"diskMem{number}Tree"
        tree_refs = rope_references(
            rope_definition(directory, tree_name),
            re.compile(rf"diskMem{number}(?:Start|InitTree|End)"))
        expected_tree = [f"diskMem{number}Start",
                         f"diskMem{number}InitTree",
                         f"diskMem{number}End"]
        if tree_refs != expected_tree:
            raise ValueError(f"{tree_name} is not start/init/end in order")
        init_refs = rope_references(
            rope_definition(directory, f"diskMem{number}InitTree"),
            re.compile(rf"diskMem{number}Init\d{{4}}"))
        expected_init = sorted(
            name for name in values
            if re.fullmatch(rf"diskMem{number}Init\d{{4}}", name))
        if init_refs != expected_init:
            raise ValueError(f"memory {number} init leaves are not in order")
        names += [f"diskMem{number}Start", *init_refs,
                  f"diskMem{number}End"]

    wire_tree_name = ("diskWireLineTree" if "def diskWireLineTree" in root
                      else "diskWireTree")
    wire_top_refs = rope_references(
        rope_definition(directory, wire_tree_name),
        re.compile(r"diskWire(?:Block|TreeChunk)\d{4}"))
    wire_refs = []
    for reference in wire_top_refs:
        if re.fullmatch(r"diskWireTreeChunk\d{4}", reference):
            wire_refs += rope_references(
                rope_definition(directory, reference),
                re.compile(r"diskWireBlock\d{4}"))
        else:
            wire_refs.append(reference)
    expected_wires = sorted(
        name for name in values if re.fullmatch(r"diskWireBlock\d{4}", name))
    if wire_refs != expected_wires:
        raise ValueError("wire leaves are not in source order")
    suffix_refs = list_concat_references(
        directory, "diskSuffix",
        re.compile(r"disk(?:AlwaysStart|RegResetBlock\d{4}|AlwaysMiddle|"
                   r"RegNextBlock\d{4}|MemWrites|AlwaysEnd|OutBlock\d{4}|"
                   r"ModuleEnd)"))
    return names + wire_refs + suffix_refs


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("rtl", type=Path)
    parser.add_argument("generated", type=Path)
    args = parser.parse_args()
    values = declarations(args.generated)
    names = ordered_names(args.generated, values)
    missing = [name for name in names if name not in values]
    if missing:
        raise SystemExit(f"missing disk declarations: {', '.join(missing)}")
    used = {name for name in names}
    unexpected = sorted(name for name in values if name not in used)
    if unexpected:
        raise SystemExit(f"unbound disk declarations: {', '.join(unexpected)}")
    certified = "\n".join(line for name in names for line in values[name]).encode()
    with tempfile.NamedTemporaryFile() as reconstructed:
        reconstructed.write(certified)
        reconstructed.flush()
        comparison = subprocess.run(
            ["cmp", "-s", reconstructed.name, str(args.rtl)], check=False)
    if comparison.returncode != 0:
        if comparison.returncode > 1:
            raise SystemExit(f"cmp failed with status {comparison.returncode}")
        actual = args.rtl.read_bytes()
        mismatch = next((i for i, pair in enumerate(zip(certified, actual))
                         if pair[0] != pair[1]), min(len(certified), len(actual)))
        raise SystemExit(
            f"byte mismatch at offset {mismatch}: certified={len(certified)} "
            f"actual={len(actual)}")
    print(f"exact cmp binding passed: {args.rtl} ({len(certified)} bytes)")


if __name__ == "__main__":
    main()
