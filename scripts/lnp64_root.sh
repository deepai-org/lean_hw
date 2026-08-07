#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# The ONE place this repo says where `lnp64` is.
#
# Loom and the machines depend on the ISA repo for the assembler, the
# emulator, the built clang and the opcode tables. That dependency is
# deliberate and one-way (see REPO_BOUNDARY.md): an implementation may depend
# on its specification and toolchain; the specification may not depend on any
# one implementation. Nothing in `lnp64` references this repo.
#
# Override with LNP64_ROOT for a checkout that is not the sibling directory.
LNP64_ROOT="${LNP64_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../lnp64" 2>/dev/null && pwd)}"
LNP64_BIN="${LNP64_BIN:-$LNP64_ROOT/target/release/lnp64}"
export LNP64_ROOT LNP64_BIN
