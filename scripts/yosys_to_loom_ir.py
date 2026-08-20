#!/usr/bin/env python3
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
"""Translate identified Yosys JSON into Loom's neutral import JSON.

Yosys and this adapter are untrusted.  The emitted tree is consumed by Loom's
fail-closed `ImportIR` validator/lowering and must still pass original-vs-Loom
RTL equivalence.  Unsupported cells are retained as source-located blockers;
they are never guessed or dropped.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from dataclasses import dataclass
from typing import Any


SEQUENTIAL = {"$dff", "$dffe", "$sdff", "$sdffe", "$sdffce", "$adff", "$adffe"}
SUPPORTED_COMB = {
    "$not": "bit_not", "$neg": "negate",
    "$and": "bit_and", "$or": "bit_or", "$xor": "bit_xor",
    "$add": "add", "$sub": "sub", "$mul": "mul", "$div": "unsigned_div",
    "$mod": "unsigned_rem", "$shl": "shift_left", "$shr": "logical_shift_right",
    "$shift": "normalized_signed_direction_shift",
    "$sshr": "normalized_arithmetic_shift_right",
    "$eq": "equal", "$lt": "less_than", "$mux": "mux",
    "$logic_and": "logical_and", "$logic_or": "logical_or",
    "$logic_not": "logical_not", "$reduce_and": "reduce_and",
    "$reduce_or": "reduce_bool", "$reduce_bool": "reduce_bool",
    "$ne": "not_equal", "$ge": "greater_equal", "$gt": "greater_than",
    "$le": "less_equal",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def decode_parameter(value: Any, default: int = 0) -> int:
    if isinstance(value, int):
        return value
    if not isinstance(value, str):
        return default
    clean = value.replace("x", "0").replace("z", "0")
    try:
        return int(clean, 2)
    except ValueError:
        try:
            return int(value, 0)
        except ValueError:
            return default


LOCATION = re.compile(r"^(.*?):(\d+)\.(\d+)-(\d+)\.(\d+)$")


def location(src: str, fallback: str = "<yosys>") -> dict[str, Any]:
    first = src.split("|")[0].strip() if src else ""
    match = LOCATION.match(first)
    if not match:
        return {"file": fallback, "start_line": 1, "start_column": 0,
                "end_line": 1, "end_column": 0}
    return {"file": match.group(1), "start_line": int(match.group(2)),
            "start_column": int(match.group(3)), "end_line": int(match.group(4)),
            "end_column": int(match.group(5))}


def literal(width: int, value: int, src: dict[str, Any]) -> dict[str, Any]:
    return {"kind": "literal", "width": width, "value": value, "source": src}


def signal(width: int, name: str, src: dict[str, Any]) -> dict[str, Any]:
    return {"kind": "signal", "width": width, "name": name, "source": src}


def slice_expr(value: dict[str, Any], offset: int, width: int,
               src: dict[str, Any]) -> dict[str, Any]:
    if offset == 0 and value["width"] == width:
        return value
    return {"kind": "slice", "width": width, "value": value,
            "offset": offset, "source": src}


def resize(value: dict[str, Any], width: int, signed: bool,
           src: dict[str, Any]) -> dict[str, Any]:
    if value["width"] == width:
        return value
    if value["width"] < width:
        return {"kind": "sign_extend" if signed else "zero_extend",
                "width": width, "value": value, "source": src}
    return slice_expr(value, 0, width, src)


def unary(width: int, op: str, value: dict[str, Any],
          src: dict[str, Any]) -> dict[str, Any]:
    return {"kind": "unary", "width": width, "op": op,
            "value": value, "source": src}


def binary(width: int, op: str, left: dict[str, Any], right: dict[str, Any],
           src: dict[str, Any]) -> dict[str, Any]:
    return {"kind": "binary", "width": width, "op": op,
            "left": left, "right": right, "source": src}


def booleanize(value: dict[str, Any], src: dict[str, Any]) -> dict[str, Any]:
    return unary(1, "reduce_bool", value, src)


def shifted_operand(value: dict[str, Any], amount: dict[str, Any], width: int,
                    signed_value: bool, src: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    """Put a shift value and amount in one width without losing amount bits."""
    work_width = max(value["width"], amount["width"], width)
    return (resize(value, work_width, signed_value, src),
            resize(amount, work_width, False, src))


def arithmetic_shift_right(value: dict[str, Any], amount: dict[str, Any],
                           width: int, signed_value: bool,
                           src: dict[str, Any]) -> dict[str, Any]:
    base_width = max(value["width"], width)
    # A logical shift over a sign extension twice as wide preserves the
    # shifted-in sign bits for every in-range amount. The explicit out-of-
    # range branch below handles amounts at least the result's base width.
    work_width = max(base_width * 2 if signed_value else base_width,
                     amount["width"])
    value = resize(value, work_width, signed_value, src)
    amount = resize(amount, work_width, False, src)
    shifted = binary(value["width"], "logical_shift_right", value, amount, src)
    if signed_value:
        sign = slice_expr(value, value["width"] - 1, 1, src)
        fill = {"kind": "mux", "width": value["width"], "condition": sign,
                "yes": literal(value["width"], (1 << value["width"]) - 1, src),
                "no": literal(value["width"], 0, src), "source": src}
        in_range = binary(1, "unsigned_less_than", amount,
                          literal(value["width"], base_width, src), src)
        shifted = {"kind": "mux", "width": value["width"],
                   "condition": in_range, "yes": shifted, "no": fill,
                   "source": src}
    return resize(shifted, width, signed_value, src)


@dataclass
class Driver:
    cell_name: str
    port: str
    offset: int


class ModuleTranslator:
    def __init__(self, name: str, module: dict[str, Any], modules: dict[str, Any]):
        self.name = name
        self.module = module
        self.modules = modules
        self.module_source = location(module.get("attributes", {}).get("src", ""))
        self.netnames = module.get("netnames", {})
        self.cells = module.get("cells", {})
        self.bit_names: dict[int, list[tuple[str, int, int]]] = {}
        self.inputs: dict[tuple[Any, ...], tuple[str, dict[str, Any]]] = {}
        self.registers: dict[tuple[Any, ...], str] = {}
        self.drivers: dict[int, Driver] = {}
        self.expression_cache: dict[tuple[str, str], dict[str, Any]] = {}
        self.in_progress: set[tuple[str, str]] = set()
        self.unsupported: list[dict[str, Any]] = []
        self._index()

    def _index(self) -> None:
        for name, net in self.netnames.items():
            bits = net.get("bits", [])
            for offset, bit in enumerate(bits):
                if isinstance(bit, int):
                    self.bit_names.setdefault(bit, []).append((name, offset, len(bits)))
        for name, port in self.module.get("ports", {}).items():
            if port.get("direction") == "input":
                src = self.source_for_bits(port.get("bits", []))
                self.inputs[tuple(port.get("bits", []))] = (name, src)
        for cell_name, cell in self.cells.items():
            for port, direction in cell.get("port_directions", {}).items():
                if direction != "output":
                    continue
                for offset, bit in enumerate(cell.get("connections", {}).get(port, [])):
                    if isinstance(bit, int):
                        if bit in self.drivers:
                            self.block("multiple_drivers", f"bit {bit} has multiple cell drivers",
                                       cell.get("attributes", {}).get("src", ""))
                        self.drivers[bit] = Driver(cell_name, port, offset)

    def source_for_bits(self, bits: list[Any]) -> dict[str, Any]:
        target = tuple(bits)
        choices = []
        for _, net in self.netnames.items():
            if tuple(net.get("bits", [])) == target:
                choices.append(net.get("attributes", {}).get("src", ""))
        return location(next((item for item in choices if item), ""),
                        self.module_source["file"])

    def public_name(self, bits: list[Any], fallback: str) -> str:
        target = tuple(bits)
        names = [name for name, net in self.netnames.items()
                 if tuple(net.get("bits", [])) == target and not name.startswith("$")]
        return sorted(names, key=lambda item: (len(item), item))[0] if names else fallback

    @staticmethod
    def legal_identifier(name: str) -> str:
        """Injectively encode arbitrary UTF-8 Yosys names as HDL identifiers."""
        return "_h" + name.encode("utf-8").hex()

    def instance_net(self, cell_name: str, port: str) -> str:
        return ("__loom_child_" + self.legal_identifier(cell_name) +
                "__" + self.legal_identifier(port))

    def block(self, kind: str, detail: str, src: str | dict[str, Any]) -> None:
        source = src if isinstance(src, dict) else location(src, self.module_source["file"])
        record = {"kind": kind, "detail": detail, "source": source}
        if record not in self.unsupported:
            self.unsupported.append(record)

    def constant(self, bits: list[Any], src: dict[str, Any]) -> dict[str, Any] | None:
        if not all(isinstance(bit, str) for bit in bits):
            return None
        if any(bit not in ("0", "1") for bit in bits):
            self.block("four_state_constant", f"unsupported constant bits {bits}", src)
            return literal(len(bits), 0, src)
        value = sum((1 << index) for index, bit in enumerate(bits) if bit == "1")
        return literal(len(bits), value, src)

    def vector_alias(self, bits: list[Any], aliases: dict[tuple[Any, ...], Any],
                     src: dict[str, Any]) -> dict[str, Any] | None:
        exact = aliases.get(tuple(bits))
        if exact is not None:
            name = exact[0] if isinstance(exact, tuple) else exact
            return signal(len(bits), name, src)
        if len(bits) != 1 or not isinstance(bits[0], int):
            return None
        bit = bits[0]
        for vector, entry in aliases.items():
            if bit in vector:
                name = entry[0] if isinstance(entry, tuple) else entry
                whole = signal(len(vector), name, src)
                return slice_expr(whole, vector.index(bit), 1, src)
        return None

    def expr(self, bits: list[Any], src: dict[str, Any] | None = None) -> dict[str, Any]:
        src = src or self.source_for_bits(bits)
        if not bits:
            self.block("zero_width", "empty signal vector", src)
            return literal(1, 0, src)
        result = self.constant(bits, src)
        if result is not None:
            return result
        result = self.vector_alias(bits, self.inputs, src)
        if result is not None:
            return result
        result = self.vector_alias(bits, self.registers, src)
        if result is not None:
            return result
        exact_driver = None
        for cell_name, cell in self.cells.items():
            for port, direction in cell.get("port_directions", {}).items():
                if direction == "output" and tuple(cell.get("connections", {}).get(port, [])) == tuple(bits):
                    exact_driver = (cell_name, port)
                    break
            if exact_driver:
                break
        if exact_driver:
            return self.cell_expr(*exact_driver)
        if len(bits) == 1 and isinstance(bits[0], int) and bits[0] in self.drivers:
            driver = self.drivers[bits[0]]
            whole = self.cell_expr(driver.cell_name, driver.port)
            return slice_expr(whole, driver.offset, 1, src)
        # Yosys vectors are LSB-first. Build the semantic vector MSB-to-LSB.
        parts = [self.expr([bit], src) for bit in reversed(bits)]
        value = parts[0]
        for part in parts[1:]:
            value = {"kind": "concat", "width": value["width"] + part["width"],
                     "high": value, "low": part, "source": src}
        return value

    def cell_expr(self, cell_name: str, port: str) -> dict[str, Any]:
        key = (cell_name, port)
        if key in self.expression_cache:
            return self.expression_cache[key]
        cell = self.cells[cell_name]
        src = location(cell.get("attributes", {}).get("src", ""), self.module_source["file"])
        bits = cell.get("connections", {}).get(port, [])
        width = len(bits)
        if key in self.in_progress:
            self.block("combinational_cycle", f"cycle at {cell_name}.{port}", src)
            return literal(max(width, 1), 0, src)
        self.in_progress.add(key)
        kind = cell.get("type", "")
        connections = cell.get("connections", {})
        params = cell.get("parameters", {})
        if kind in SEQUENTIAL:
            name = self.registers.get(tuple(bits), self.public_name(bits, cell_name.strip("\\$")))
            result = signal(width, name, src)
        elif kind in self.modules:
            result = signal(max(width, 1), self.instance_net(cell_name, port), src)
        elif kind.startswith("$mem"):
            self.block("memory_cell", f"memory cell {kind} requires memory lowering", src)
            result = literal(max(width, 1), 0, src)
        elif kind not in SUPPORTED_COMB:
            self.block("yosys_cell", f"unsupported cell type {kind}", src)
            result = literal(max(width, 1), 0, src)
        elif kind in ("$not", "$neg"):
            value = resize(self.expr(connections.get("A", []), src), width,
                           bool(decode_parameter(params.get("A_SIGNED"))), src)
            result = unary(width, SUPPORTED_COMB[kind], value, src)
        elif kind in ("$logic_not", "$reduce_and", "$reduce_or", "$reduce_bool"):
            value = self.expr(connections.get("A", []), src)
            reduced = unary(1, SUPPORTED_COMB[kind], value, src)
            result = resize(reduced, width, False, src)
        elif kind in ("$logic_and", "$logic_or"):
            left = booleanize(self.expr(connections.get("A", []), src), src)
            right = booleanize(self.expr(connections.get("B", []), src), src)
            reduced = binary(1, "bit_and" if kind == "$logic_and" else "bit_or",
                             left, right, src)
            result = resize(reduced, width, False, src)
        elif kind == "$mux":
            yes = resize(self.expr(connections.get("B", []), src), width, False, src)
            no = resize(self.expr(connections.get("A", []), src), width, False, src)
            condition = self.expr(connections.get("S", []), src)
            result = {"kind": "mux", "width": width, "condition": condition,
                      "yes": yes, "no": no, "source": src}
        elif kind == "$sshr":
            value = self.expr(connections.get("A", []), src)
            amount = self.expr(connections.get("B", []), src)
            result = arithmetic_shift_right(
                value, amount, width,
                bool(decode_parameter(params.get("A_SIGNED"))), src)
        elif kind == "$shift":
            value = self.expr(connections.get("A", []), src)
            amount_raw = self.expr(connections.get("B", []), src)
            value_signed = bool(decode_parameter(params.get("A_SIGNED")))
            amount_signed = bool(decode_parameter(params.get("B_SIGNED")))
            work_width = max(value["width"], amount_raw["width"], width)
            value = resize(value, work_width, value_signed, src)
            amount = resize(amount_raw, work_width, amount_signed, src)
            right = binary(work_width, "logical_shift_right", value, amount, src)
            if amount_signed:
                negative = slice_expr(amount, work_width - 1, 1, src)
                magnitude = unary(work_width, "negate", amount, src)
                left = binary(work_width, "shift_left", value, magnitude, src)
                shifted = {"kind": "mux", "width": work_width,
                           "condition": negative, "yes": left, "no": right,
                           "source": src}
            else:
                shifted = right
            result = resize(shifted, width, value_signed, src)
        else:
            left_signed = bool(decode_parameter(params.get("A_SIGNED")))
            right_signed = bool(decode_parameter(params.get("B_SIGNED")))
            op = SUPPORTED_COMB[kind]
            if kind in ("$eq", "$ne", "$lt", "$le", "$ge", "$gt"):
                operand_width = max(len(connections.get("A", [])), len(connections.get("B", [])))
                left = resize(self.expr(connections.get("A", []), src), operand_width,
                              left_signed, src)
                right = resize(self.expr(connections.get("B", []), src), operand_width,
                               right_signed, src)
                less_op = ("signed_less_than" if left_signed and right_signed
                           else "unsigned_less_than")
                if kind == "$eq":
                    compared = binary(1, "equal", left, right, src)
                elif kind == "$ne":
                    compared = unary(1, "logical_not",
                                     binary(1, "equal", left, right, src), src)
                elif kind == "$lt":
                    compared = binary(1, less_op, left, right, src)
                elif kind == "$gt":
                    compared = binary(1, less_op, right, left, src)
                elif kind == "$ge":
                    compared = unary(1, "logical_not",
                                     binary(1, less_op, left, right, src), src)
                else:  # $le
                    compared = unary(1, "logical_not",
                                     binary(1, less_op, right, left, src), src)
                result = resize(compared, width, False, src)
            else:
                left = resize(self.expr(connections.get("A", []), src), width,
                              left_signed, src)
                right = resize(self.expr(connections.get("B", []), src), width,
                               right_signed, src)
                result = binary(width, op, left, right, src)
        self.in_progress.remove(key)
        self.expression_cache[key] = result
        return result

    def translate(self) -> dict[str, Any]:
        registers = []
        clock_domains: set[tuple[tuple[Any, ...], bool]] = set()
        resets: set[tuple[tuple[Any, ...], bool, str]] = set()
        resetless_cells: list[str] = []
        asynchronous_cells: list[str] = []
        enable_dominant_reset_cells: list[str] = []
        sequential_cells = []
        for cell_name, cell in self.cells.items():
            kind = cell.get("type", "")
            if kind not in SEQUENTIAL:
                continue
            sequential_cells.append((cell_name, cell))
            connections = cell.get("connections", {})
            params = cell.get("parameters", {})
            q = connections.get("Q", [])
            reg_name = self.public_name(q, cell_name.strip("\\$"))
            self.registers[tuple(q)] = reg_name
            clock_domains.add((tuple(connections.get("CLK", [])),
                               bool(decode_parameter(params.get("CLK_POLARITY"), 1))))
            if kind.startswith("$adff"):
                resets.add((tuple(connections.get("ARST", [])),
                            bool(decode_parameter(params.get("ARST_POLARITY"), 1)),
                            "asynchronous"))
                asynchronous_cells.append(cell_name)
            elif kind.startswith("$sdff"):
                resets.add((tuple(connections.get("SRST", [])),
                            bool(decode_parameter(params.get("SRST_POLARITY"), 1)),
                            "synchronous"))
                if kind == "$sdffce":
                    enable_dominant_reset_cells.append(cell_name)
            else:
                resetless_cells.append(cell_name)

        if resetless_cells:
            detail = ("resetless state cannot use the current always-reset µVerilog frame: " +
                      ", ".join(sorted(resetless_cells)))
            self.block("resetless_state", detail, self.module_source)
        if resetless_cells and resets:
            self.block("mixed_reset_state",
                       "resetless and reset-bearing registers share one imported module",
                       self.module_source)
        if asynchronous_cells:
            self.block("asynchronous_reset_state",
                       "asynchronous reset state must remain behind an external contract: " +
                       ", ".join(sorted(asynchronous_cells)), self.module_source)
        if enable_dominant_reset_cells:
            self.block("enable_dominant_reset",
                       "$sdffce priority is not represented by Loom's reset-dominant frame: " +
                       ", ".join(sorted(enable_dominant_reset_cells)), self.module_source)

        for cell_name, cell in sequential_cells:
            kind = cell["type"]
            connections = cell.get("connections", {})
            params = cell.get("parameters", {})
            src = location(cell.get("attributes", {}).get("src", ""), self.module_source["file"])
            q = connections.get("Q", [])
            width = len(q)
            name = self.registers[tuple(q)]
            next_value = self.expr(connections.get("D", []), src)
            if kind in ("$dffe", "$sdffe", "$sdffce", "$adffe"):
                enable = self.expr(connections.get("EN", []), src)
                if not bool(decode_parameter(params.get("EN_POLARITY"), 1)):
                    enable = {"kind": "unary", "width": 1, "op": "bit_not",
                              "value": enable, "source": src}
                next_value = {"kind": "mux", "width": width, "condition": enable,
                              "yes": next_value, "no": signal(width, name, src),
                              "source": src}
            init = decode_parameter(params.get("SRST_VALUE",
                                    params.get("ARST_VALUE", 0)))
            registers.append({"name": name, "width": width, "init": init,
                              "next": next_value, "source": src})

        instances = []
        for cell_name, cell in self.cells.items():
            kind = cell.get("type", "")
            if kind not in self.modules:
                if kind.startswith("$mem"):
                    self.block("memory_cell", f"memory cell {kind} requires memory lowering",
                               cell.get("attributes", {}).get("src", ""))
                continue
            src = location(cell.get("attributes", {}).get("src", ""), self.module_source["file"])
            directions = cell.get("port_directions", {})
            if cell.get("parameters"):
                self.block("unelaborated_instance_parameter",
                           f"child instance {cell_name} retains parameter overrides", src)
            for port, bits in cell.get("connections", {}).items():
                if directions.get(port) == "input" and not bits:
                    self.block("unconnected_instance_input",
                               f"child input {cell_name}.{port} is unconnected", src)
            instances.append({
                "name": cell_name, "module_name": kind,
                "parameters": [{"name": name, "value": str(value)}
                               for name, value in sorted(cell.get("parameters", {}).items())],
                "connections": [
                    {"port": port, "direction": directions.get(port, "unknown"),
                     "signal": self.instance_net(cell_name, port),
                     "width": len(bits),
                     "value": self.expr(bits, src)
                        if directions.get(port) == "input" else None,
                     "source": src}
                    for port, bits in sorted(cell.get("connections", {}).items())
                    if bits or directions.get(port) != "output"
                ], "source": src,
            })

        for cell in self.cells.values():
            kind = cell.get("type", "")
            if (kind.startswith("$") and kind not in self.modules and
                    kind not in SEQUENTIAL and kind not in SUPPORTED_COMB and
                    not kind.startswith("$mem")):
                self.block("yosys_cell", f"unsupported cell type {kind}",
                           cell.get("attributes", {}).get("src", ""))

        ports = []
        for name, port in self.module.get("ports", {}).items():
            ports.append({"name": name, "direction": port.get("direction", "unknown"),
                          "width": len(port.get("bits", [])), "semantic_type": "bits",
                          "source": self.source_for_bits(port.get("bits", []))})

        domains = []
        if len(clock_domains) > 1:
            self.block("multiple_clock_domains", f"module contains {len(clock_domains)} clock/edge pairs",
                       self.module_source)
        if clock_domains:
            clock_bits, rising = sorted(clock_domains, key=str)[0]
            clock_name = self.public_name(list(clock_bits), "clk")
            reset_record = {"kind": "resetless", "port": None, "active_high": True,
                            "source": None}
            if len(resets) > 1:
                self.block("multiple_reset_domains", f"module contains {len(resets)} reset domains",
                           self.module_source)
            if resets:
                reset_bits, active_high, reset_kind = sorted(resets, key=str)[0]
                reset_name = self.public_name(list(reset_bits), "rst")
                reset_record = {"kind": reset_kind, "port": reset_name,
                                "active_high": active_high,
                                "source": self.source_for_bits(list(reset_bits))}
            domains.append({"name": f"{self.name}_clock", "clock_port": clock_name,
                            "edge": "rising" if rising else "falling",
                            "reset": reset_record,
                            "source": self.source_for_bits(list(clock_bits))})
        # No inferred sequential cells means a genuinely stateless module.
        # The neutral IR records this as an empty domain list; Loom's checked
        # stateless lowering emits no synthetic clock/reset interface.

        outputs = []
        for name, port in self.module.get("ports", {}).items():
            if port.get("direction") == "output":
                src = self.source_for_bits(port.get("bits", []))
                outputs.append({"name": name, "width": len(port.get("bits", [])),
                                "value": self.expr(port.get("bits", []), src),
                                "source": src})
            elif port.get("direction") not in ("input", "output"):
                self.block("port_direction", f"unsupported direction on port {name}",
                           self.source_for_bits(port.get("bits", [])))

        return {"name": self.name, "ports": ports, "domains": domains,
                "registers": registers, "memories": [], "outputs": outputs,
                "instances": instances, "unsupported": self.unsupported,
                "source": self.module_source}


EXPRESSION_KINDS = {
    "literal", "signal", "unary", "binary", "mux", "slice",
    "zero_extend", "sign_extend", "concat", "memory_read",
}


def encode_module_expression_dag(module: dict[str, Any]) -> dict[str, Any]:
    """Replace recursive expression trees with a shared postorder table.

    The adapter caches cell expressions, so the semantic representation is a
    DAG. Encoding it as ordinary recursive JSON duplicates shared cones and
    becomes exponential on wide SoC modules.
    """
    expressions: list[dict[str, Any]] = []
    ids: dict[int, int] = {}

    def intern(expression: dict[str, Any]) -> int:
        identity = id(expression)
        if identity in ids:
            return ids[identity]
        kind = expression.get("kind")
        if kind not in EXPRESSION_KINDS:
            raise ValueError(f"not an import expression: {kind!r}")
        node = dict(expression)
        if kind == "unary":
            node["value"] = intern(expression["value"])
        elif kind == "binary":
            node["left"] = intern(expression["left"])
            node["right"] = intern(expression["right"])
        elif kind == "mux":
            node["condition"] = intern(expression["condition"])
            node["yes"] = intern(expression["yes"])
            node["no"] = intern(expression["no"])
        elif kind in ("slice", "zero_extend", "sign_extend"):
            node["value"] = intern(expression["value"])
        elif kind == "concat":
            node["high"] = intern(expression["high"])
            node["low"] = intern(expression["low"])
        elif kind == "memory_read":
            node["address"] = intern(expression["address"])
        expression_id = len(expressions)
        ids[identity] = expression_id
        expressions.append(node)
        return expression_id

    encoded = dict(module)
    encoded["registers"] = [
        {**register, "next": intern(register["next"])}
        for register in module["registers"]
    ]
    encoded["memories"] = [
        {**memory, "writes": [
            {**write, "enable": intern(write["enable"]),
             "address": intern(write["address"]), "data": intern(write["data"])}
            for write in memory["writes"]
        ]}
        for memory in module["memories"]
    ]
    encoded["outputs"] = [
        {**output, "value": intern(output["value"])}
        for output in module["outputs"]
    ]
    encoded["instances"] = [
        {**instance, "connections": [
            {**connection,
             "value": (intern(connection["value"])
                       if connection["value"] is not None else None)}
            for connection in instance["connections"]
        ]}
        for instance in module["instances"]
    ]
    encoded["expressions"] = expressions
    return encoded


def main() -> int:
    # Wide Yosys vectors can become exact, deeply nested concat trees. Python's
    # default JSON recursion limit is too small for real SoC packages.
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 100_000))
    parser = argparse.ArgumentParser()
    parser.add_argument("--yosys-json", type=pathlib.Path, required=True)
    parser.add_argument("--inventory", type=pathlib.Path, required=True)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--module")
    selection.add_argument("--package-top")
    parser.add_argument("--output", type=pathlib.Path, required=True)
    parser.add_argument("--manifest-output", type=pathlib.Path)
    args = parser.parse_args()

    yosys_bytes = args.yosys_json.read_bytes()
    inventory_bytes = args.inventory.read_bytes()
    inventory = json.loads(inventory_bytes)
    expected = inventory.get("frontend", {}).get("elaborated_sha256")
    actual = sha256(yosys_bytes)
    if expected != actual:
        raise SystemExit(f"elaborated JSON identity mismatch: inventory={expected} actual={actual}")
    design = json.loads(yosys_bytes)
    modules = design.get("modules", {})
    selected_top = args.module or args.package_top
    if selected_top not in modules:
        raise SystemExit(f"module not found in elaborated design: {selected_top}")
    common_frontend = {
        "name": "yosys-json",
        "version": inventory.get("frontend", {}).get("tool", "unknown"),
        "source_set_sha256": inventory.get("source_set_sha256", ""),
        "inventory_sha256": sha256(inventory_bytes),
        "elaborated_sha256": actual,
        "assumptions": [
            "Yosys correctly parsed and elaborated the identified RTL",
            "this adapter correctly translated supported Yosys cells",
            "original-vs-emitted formal equivalence remains required",
        ],
    }
    if args.module:
        translated = ModuleTranslator(args.module, modules[args.module], modules).translate()
        translated_modules = [translated]
        report = {"schema": 1, "frontend": common_frontend, "module": translated}
    else:
        translated_modules = []
        for name, module in sorted(modules.items()):
            translated = ModuleTranslator(name, module, modules).translate()
            translated_modules.append(encode_module_expression_dag(translated))
        report = {
            "schema": 2,
            "frontend": common_frontend,
            "package": {
                "top": args.package_top,
                "modules": translated_modules,
                "source": location(
                    modules[args.package_top].get("attributes", {}).get("src", "")),
            },
        }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    manifest_path = args.manifest_output or pathlib.Path(str(args.output) + ".manifest.json")
    source_root = pathlib.Path(inventory.get("source_root", "."))
    source_artifacts = []
    for source in inventory.get("sources", []):
        path = pathlib.Path(source.get("path", ""))
        resolved = path if path.is_absolute() else source_root / path
        source_artifacts.append({
            "role": "source",
            "path": resolved.resolve().as_posix(),
            "sha256": source.get("sha256", ""),
            "bytes": source.get("bytes", 0),
        })
    manifest = {
        "schema": 1,
        "module": selected_top,
        "frontend": "scripts/yosys_to_loom_ir.py",
        "version": inventory.get("frontend", {}).get("tool", "unknown"),
        "invocation": sys.argv,
        "artifacts": source_artifacts + [
            {"role": "inventory", "path": args.inventory.resolve().as_posix(),
             "sha256": sha256(inventory_bytes), "bytes": len(inventory_bytes)},
            {"role": "elaborated_yosys_json", "path": args.yosys_json.resolve().as_posix(),
             "sha256": actual, "bytes": len(yosys_bytes)},
            {"role": "neutral_import_ir", "path": args.output.resolve().as_posix(),
             "sha256": sha256(args.output.read_bytes()),
             "bytes": args.output.stat().st_size},
        ],
        "assumptions": common_frontend["assumptions"],
    }
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    unsupported_count = sum(len(module["unsupported"]) for module in translated_modules)
    status = "PASS" if unsupported_count == 0 else "BLOCKED"
    kind = "module" if args.module else "package"
    print(f"YOSYS_TO_LOOM_IR_{status} {kind}={selected_top} "
          f"unsupported={unsupported_count} sha256={sha256(args.output.read_bytes())} "
          f"manifest={manifest_path}")
    return 0 if status == "PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
