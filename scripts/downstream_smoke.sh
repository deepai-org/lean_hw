#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Build a fresh external Lake package against this checkout. The symlink gives
# the fixture a stable ../loom dependency without embedding an absolute path.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

ln -s "$root" "$tmp/loom"
cp -R "$root/scripts/downstream-smoke" "$tmp/consumer"
mkdir -p "$tmp/consumer/.lake"
ln -s "$root/.lake/packages" "$tmp/consumer/.lake/packages"

cd "$tmp/consumer"
lake update loom
lake build

echo "downstream-smoke: OK"
