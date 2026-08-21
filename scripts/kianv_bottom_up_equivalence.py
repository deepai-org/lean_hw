#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Run hash-bound bottom-up equivalence for every KianV specialization."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tempfile
import time


IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")


def digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encoded_identifier(name: str) -> str:
    return "_loom_u" + "_".join(str(byte) for byte in name.encode())


def module_name(name: str, top: str) -> str:
    return name if name == top and IDENTIFIER.fullmatch(name) else encoded_identifier(name)


def instance_name(name: str) -> str:
    return "u" + encoded_identifier(name)


def yosys_id(name: str) -> str:
    return "\\" + name


def yosys_module_id(name: str) -> str:
    # Yosys JSON module keys such as `$paramod$...\\foo` are already command
    # identifiers; prefixing another RTLIL escape changes their identity.
    if any(character.isspace() or character in ";#" for character in name):
        raise ValueError(f"unsafe Yosys module identifier: {name!r}")
    return name


def state_pairs(package: dict, root: dict, recursive: bool = False) -> list[dict]:
    modules = {module["name"]: module for module in package["modules"]}
    pairs: list[dict] = []
    next_memory_group = 0

    def visit(module: dict, gold_prefix: str, revised_prefix: str) -> None:
        nonlocal next_memory_group
        domains = module["domains"]
        for relation in module.get("register_equivalence", []):
            if len(domains) > 1:
                indexes = [index for index, domain in enumerate(domains)
                           if domain["name"] == relation.get("domain")]
                if len(indexes) != 1:
                    raise ValueError(f"register domain is not unique in {module['name']}")
                body = f"u_loom_domain_{indexes[0]}."
            else:
                body = "u_loom_body."
            pairs.append({"kind": "register",
                          "gold": gold_prefix + relation["original"],
                          "gold_offset": relation.get("original_offset", 0),
                          "revised": revised_prefix + body + relation["loom"],
                          "width": relation["width"]})
        if module.get("memory_equivalence") and len(domains) > 1:
            raise ValueError(f"multi-domain memory relation unsupported in {module['name']}")
        for relation in module.get("memory_equivalence", []):
            memory_index = next_memory_group
            next_memory_group += 1
            for address in range(relation["size"]):
                pairs.append({"kind": "memory",
                              "memory_index": memory_index,
                              "address": address,
                              "gold": f"{gold_prefix}{relation['original']}[{address}]",
                              "revised": (f"{revised_prefix}u_loom_body."
                                          f"{relation['word_memory']}[{address}]"),
                              "width": relation["width"]})
        if recursive:
            for instance in module["instances"]:
                child = modules.get(instance["module_name"])
                if child is None:
                    raise ValueError(f"missing child {instance['module_name']}")
                visit(child, gold_prefix + instance["name"] + ".",
                      revised_prefix + instance_name(instance["name"]) + ".")
    visit(root, "", "")
    if len({(pair["gold"], pair["revised"]) for pair in pairs}) != len(pairs):
        raise ValueError(f"duplicate state relation below {root['name']}")
    return pairs


def register_expression(pair: dict, side: str) -> str:
    name = pair[side]
    if side == "revised":
        return name
    offset = pair["gold_offset"]
    if pair["width"] == 1:
        return f"{name}[{offset}]"
    return f"{name}[{offset + pair['width'] - 1}:{offset}]"


def add_register_relation_wires(lines: list[str], pairs: list[dict],
                                side: str) -> None:
    label = "gold" if side == "gold" else "gate"
    for index, pair in enumerate(pairs):
        if pair["kind"] != "register":
            continue
        wire = f"__loom_state_{label}_{index}"
        lines += [f"add -wire {wire} {pair['width']}",
                  f"connect -set {wire} {register_expression(pair, side)}",
                  f"setattr -set keep 1 w:{wire}"]


def add_memory_relation_wires(lines: list[str], pairs: list[dict], side: str) -> None:
    """Expose exact memory state in one packed wire per source memory.

    A word-per-wire representation makes Yosys repeatedly walk the complete
    module for every word and produces hundreds of independent `$equiv`
    cells.  Packing does not abstract any state: every word occupies one
    disjoint slice, while the proof engine receives only one correspondence
    relation per memory.
    """
    label = "gold" if side == "gold" else "gate"
    groups: dict[int, list[dict]] = {}
    for pair in pairs:
        if pair["kind"] == "memory":
            groups.setdefault(pair["memory_index"], []).append(pair)
    for memory_index, words in groups.items():
        words.sort(key=lambda pair: pair["address"])
        width = sum(pair["width"] for pair in words)
        wire = f"__loom_memory_{label}_{memory_index}"
        lines.append(f"add -wire {wire} {width}")
        offset = 0
        for pair in words:
            msb = offset + pair["width"] - 1
            lines.append(f"connect -nomap -set {wire}[{msb}:{offset}] "
                         f"{yosys_id(pair[side])}")
            offset = msb + 1
        lines.append(f"setattr -set keep 1 w:{wire}")


def memory_group_indexes(pairs: list[dict]) -> list[int]:
    return sorted({pair["memory_index"] for pair in pairs
                   if pair["kind"] == "memory"})


def stable_bit_expression(raw_module: dict, bit: object) -> str:
    if isinstance(bit, str):
        if bit not in ("0", "1"):
            raise ValueError(f"unresolved four-state child connection bit {bit!r}")
        return f"1'{bit}"
    choices = []
    for name, net in raw_module.get("netnames", {}).items():
        for offset, candidate in enumerate(net.get("bits", [])):
            if candidate == bit:
                choices.append((name.startswith("$"), len(net.get("bits", [])),
                                len(name), name, offset))
    if not choices:
        raise ValueError(f"child connection bit {bit!r} has no stable public net")
    _, _, _, name, offset = sorted(choices)[0]
    return f"{name}[{offset}]"


def all_bit_expressions(raw_module: dict, bit: object) -> list[str]:
    if isinstance(bit, str):
        return [stable_bit_expression(raw_module, bit)]
    expressions = []
    for name, net in raw_module.get("netnames", {}).items():
        for offset, candidate in enumerate(net.get("bits", [])):
            if candidate == bit:
                expressions.append(f"{name}[{offset}]")
    if not expressions:
        raise ValueError(f"child output bit {bit!r} has no net alias")
    return expressions


def revised_connection_expression(module: dict, connection: dict, bit: int) -> str:
    value = connection.get("value")
    expression = (module["expressions"][value]
                  if isinstance(value, int) and value < len(module["expressions"])
                  else None)
    direct_names = {domain["clock_port"] for domain in module["domains"]}
    direct_names.update(domain["reset"]["port"] for domain in module["domains"]
                        if domain["reset"].get("port") is not None)
    if (connection["direction"] == "input" and expression is not None and
            expression.get("kind") == "signal" and expression.get("name") in direct_names):
        return f"{expression['name']}[{bit}]"
    body = "u_loom_body" if len(module["domains"]) <= 1 else "u_loom_comb"
    return f"{body}.{connection['signal']}[{bit}]"


def add_child_harness(lines: list[str], module: dict, raw_module: dict,
                      side: str) -> None:
    """Cut immediate children at their ports for compositional proof.

    Child outputs become shared miter inputs (the already-proven child
    contract), while child inputs become additional miter outputs that the
    parent must prove equal. This prevents re-flattening a proven child at
    every ancestor and records exact coverage for every instance port.
    """
    revised_bases: dict[tuple[int, int], str] = {}
    if side == "revised":
        for instance_index, instance in enumerate(module["instances"]):
            for connection_index, connection in enumerate(instance["connections"]):
                expression = revised_connection_expression(module, connection, 0)
                base = expression.rsplit("[", 1)[0]
                if "." in base:
                    safe = f"__loom_child_endpoint_{instance_index}_{connection_index}"
                    lines.append(f"rename {yosys_id(base)} {safe}")
                    base = safe
                revised_bases[(instance_index, connection_index)] = base

    # Remove every child before reconnecting any cut. A later deletion can
    # otherwise clear an earlier harness connection on a shared inter-child
    # net, depending on the source instance order.
    for instance in module["instances"]:
        cell = instance["name"] if side == "gold" else instance_name(instance["name"])
        lines.append(f"delete c:{yosys_id(cell)}")

    for instance_index, instance in enumerate(module["instances"]):
        raw_cell = raw_module["cells"][instance["name"]]
        for connection_index, connection in enumerate(instance["connections"]):
            direction = connection["direction"]
            if direction not in ("input", "output"):
                raise ValueError("compositional harness supports input/output child ports")
            harness = f"__loom_child_contract_{instance_index}_{connection_index}"
            port_kind = "output" if direction == "input" else "input"
            lines.append(f"add -{port_kind} {harness} {connection['width']}")
            if side == "revised":
                endpoint = revised_bases[(instance_index, connection_index)]
                if direction == "input":
                    lines.append(f"connect -nomap -set {yosys_id(harness)} "
                                 f"{yosys_id(endpoint)}")
                else:
                    lines.append(f"connect -nomap -set {yosys_id(endpoint)} "
                                 f"{yosys_id(harness)}")
                continue
            raw_bits = raw_cell["connections"][connection["port"]]
            for bit in range(connection["width"]):
                endpoint = stable_bit_expression(raw_module, raw_bits[bit])
                if direction == "input":
                    lines.append(f"connect -nomap -set {harness}[{bit}] {endpoint}")
                else:
                    # A removed output cell can leave several formerly aliased
                    # source nets disconnected. Re-drive every retained alias;
                    # downstream logic and module outputs need not use the
                    # shortest alias selected above.
                    for output_endpoint in all_bit_expressions(raw_module, raw_bits[bit]):
                        lines.append(f"connect -nomap -set {output_endpoint} "
                                     f"{harness}[{bit}]")


def script_for(elaborated: pathlib.Path, emitted: pathlib.Path,
               package: dict, module: dict, raw_module: dict, depth: int,
               flatten_hierarchy: bool = False) -> str:
    original = module["name"]
    revised = module_name(original, package["top"])
    pairs = state_pairs(package, module, recursive=flatten_hierarchy)
    has_memory = bool(memory_group_indexes(pairs))
    lines = [
        f"read_json {elaborated.resolve()}",
        f"hierarchy -check -top {yosys_module_id(original)}",
        "proc",
    ]
    if flatten_hierarchy:
        lines += ["flatten", f"cd {yosys_module_id(original)}"]
    else:
        lines += [f"cd {yosys_module_id(original)}"]
        add_child_harness(lines, module, raw_module, "gold")
    add_register_relation_wires(lines, pairs, "gold")
    if has_memory:
        lines += ["opt -full", "memory -nowiden"]
        add_memory_relation_wires(lines, pairs, "gold")
        lines += ["setundef -zero", "opt -full", "opt_clean -purge", "cd .."]
    else:
        lines += ["cd ..", "memory", f"cd {yosys_module_id(original)}"]
        add_memory_relation_wires(lines, pairs, "gold")
        lines += ["cd ..", "setundef -zero", "opt_clean -purge"]
    lines += [f"rename {yosys_module_id(original)} loom_equiv_gold",
        "design -stash loom_gold_design",
        f"read_verilog {emitted.resolve()}",
        f"hierarchy -check -top {revised}",
        "proc",
    ]
    if flatten_hierarchy:
        lines += ["flatten", f"cd {revised}"]
    else:
        lines += [f"cd {revised}"]
        body_cells = (["u_loom_body"] if len(module["domains"]) <= 1 else
                      ["u_loom_comb"] + [f"u_loom_domain_{index}"
                                          for index in range(len(module["domains"]))])
        lines += [f"flatten c:{cell}" for cell in body_cells]
        add_child_harness(lines, module, raw_module, "revised")
    add_register_relation_wires(lines, pairs, "revised")
    if has_memory:
        lines += ["opt -full", "memory -nowiden"]
        add_memory_relation_wires(lines, pairs, "revised")
        lines += ["setundef -zero", "opt -full", "opt_clean -purge", "cd .."]
    else:
        lines += ["cd ..", "memory", f"cd {revised}"]
        add_memory_relation_wires(lines, pairs, "revised")
        lines += ["cd ..", "setundef -zero", "opt_clean -purge"]
    lines += [f"rename {revised} loom_equiv_revised",
        "design -stash loom_revised_design",
        "design -copy-from loom_gold_design -as loom_equiv_gold loom_equiv_gold",
        "design -copy-from loom_revised_design -as loom_equiv_revised loom_equiv_revised",
        "equiv_make loom_equiv_gold loom_equiv_revised loom_equiv_miter",
        "hierarchy -top loom_equiv_miter", "cd loom_equiv_miter",
    ]
    for index, pair in enumerate(pairs):
        # Optimization may remove state that is unobservable at this module
        # boundary. `-try` skips only an absent side; every surviving pair is
        # still inserted as an induction invariant and must prove.
        if pair["kind"] != "register":
            continue
        gold = f"__loom_state_gold_{index}_gold"
        revised_state = f"__loom_state_gate_{index}_gate"
        lines.append(f"equiv_add -try {yosys_id(gold)} {yosys_id(revised_state)}")
    for memory_index in memory_group_indexes(pairs):
        gold = f"__loom_memory_gold_{memory_index}_gold"
        revised_state = f"__loom_memory_gate_{memory_index}_gate"
        lines.append(f"equiv_add -try {yosys_id(gold)} {yosys_id(revised_state)}")
    lines.append("cd ..")
    if memory_group_indexes(pairs):
        # Every memory bit is present in the asserted relation, so equality is
        # a one-step inductive invariant.  Proving it directly avoids asking
        # equiv_simple to rediscover thousands of individual word invariants.
        lines += ["equiv_miter -assert loom_equiv_assert",
                  "hierarchy -top loom_equiv_assert",
                  "sat -seq 1 -tempinduct -set-init-zero -set-def-inputs "
                  "-prove-asserts -verify"]
    else:
        lines += [f"equiv_simple -seq {depth}",
                  f"equiv_induct -seq {depth}", "equiv_status -assert"]
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--elaborated", type=pathlib.Path, required=True)
    parser.add_argument("--package", type=pathlib.Path, required=True)
    parser.add_argument("--emitted", type=pathlib.Path, required=True)
    parser.add_argument("--output-dir", type=pathlib.Path, required=True)
    parser.add_argument("--seq", type=int, default=12,
                        help="equiv induction depth for non-memory modules (default: 12)")
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--module", action="append", default=[])
    parser.add_argument("--leaves-only", action="store_true")
    parser.add_argument("--external-contract", type=pathlib.Path)
    parser.add_argument("--flatten-module", action="append", default=[])
    parser.add_argument("--yosys", default="yosys")
    args = parser.parse_args()
    document = json.loads(args.package.read_text(encoding="utf-8"))
    elaborated_document = json.loads(args.elaborated.read_text(encoding="utf-8"))
    package = document["package"]
    contracted_modules: dict[str, dict] = {}
    if args.external_contract is not None:
        external = json.loads(args.external_contract.read_text(encoding="utf-8"))
        contracted_modules[external["component"] + "_wrapper"] = external
    selected = package["modules"]
    if args.module:
        wanted = set(args.module)
        selected = [module for module in selected if module["name"] in wanted]
        if {module["name"] for module in selected} != wanted:
            parser.error("requested module is absent from the exact package")
    if args.leaves_only:
        selected = [module for module in selected if not module["instances"]]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    results = []
    for index, module in enumerate(selected, 1):
        safe = hashlib.sha256(module["name"].encode()).hexdigest()[:16]
        log_path = args.output_dir / f"{index:03d}-{safe}.log"
        if module["name"] in contracted_modules:
            external = contracted_modules[module["name"]]
            log_path.write_text(
                f"EXTERNAL_CONTRACT {external['contract']}\n"
                f"CONTRACT_SHA256 {digest(args.external_contract)}\n",
                encoding="utf-8")
            result = {"module": module["name"], "status": "CONTRACT",
                      "seconds": 0.0, "state_pairs": len(state_pairs(package, module)),
                      "child_instances": len(module["instances"]),
                      "child_ports": sum(len(instance["connections"])
                                         for instance in module["instances"]),
                      "contract": external["contract"],
                      "contract_sha256": digest(args.external_contract),
                      "log": log_path.name, "log_sha256": digest(log_path)}
            results.append(result)
            print(f"KIANV_EQUIV_CONTRACT {index}/{len(selected)} "
                  f"module={module['name']} contract={external['contract']}", flush=True)
            continue
        flatten_hierarchy = module["name"] in set(args.flatten_module)
        script = script_for(args.elaborated, args.emitted, package, module,
                            elaborated_document["modules"][module["name"]], args.seq,
                            flatten_hierarchy=flatten_hierarchy)
        started = time.monotonic()
        try:
            with (tempfile.NamedTemporaryFile("w", suffix=".ys") as ys,
                  log_path.open("w", encoding="utf-8") as log):
                ys.write(script)
                ys.flush()
                run = subprocess.run([args.yosys, "-Q", "-s", ys.name], text=True,
                                     stdout=log, stderr=subprocess.STDOUT,
                                     timeout=args.timeout)
            status = "PASS" if run.returncode == 0 else "FAIL"
        except subprocess.TimeoutExpired:
            status = "TIMEOUT"
        module_pairs = state_pairs(package, module, recursive=flatten_hierarchy)
        result = {"module": module["name"], "status": status,
                  "seconds": round(time.monotonic() - started, 3),
                  "state_pairs": len(module_pairs),
                  "proof_mode": ("flatten" if flatten_hierarchy else "compositional"),
                  "proof_strategy": ("memory_relational_induction"
                                      if memory_group_indexes(module_pairs)
                                      else "equiv_simple_induct"),
                  "child_instances": len(module["instances"]),
                  "child_ports": sum(len(instance["connections"])
                                     for instance in module["instances"]),
                  "log": log_path.name, "log_sha256": digest(log_path)}
        results.append(result)
        print(f"KIANV_EQUIV_{status} {index}/{len(selected)} module={module['name']} "
              f"state_pairs={result['state_pairs']} seconds={result['seconds']}", flush=True)
    report = {"schema": 1, "status": ("PASS" if results and
              all(result["status"] in ("PASS", "CONTRACT")
                  for result in results) else "FAIL"),
              "elaborated_sha256": digest(args.elaborated),
              "package_sha256": digest(args.package),
              "emitted_sha256": digest(args.emitted),
              "external_contract_sha256": (digest(args.external_contract)
                  if args.external_contract is not None else None),
              "selected_modules": [module["name"] for module in selected],
              "results": results}
    report_path = args.output_dir / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"KIANV_BOTTOM_UP_EQUIVALENCE_{report['status']} modules={len(results)} "
          f"report={report_path}")
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
