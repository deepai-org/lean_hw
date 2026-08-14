#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Build the independently packaged theorem before the dynamic axiom audit.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build Tools.MulticlockRelease
lake exe multiclockReleaseAudit
