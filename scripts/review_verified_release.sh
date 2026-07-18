#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Reviewer-scale release check. This deliberately samples, rather than
# claiming to check, the expensive LNP64-u register proof family.
set -euo pipefail

jobs=${1:-4}

lake build
lake test
lake exe audit
scripts/build_release_witness.sh acc8 "$jobs"
scripts/build_release_witness.sh lnp64u "$jobs" sample

echo "Tier B reviewer-scale verification passed"
echo "The full Acc8 chain passed; LNP64-u was generated, byte-bound, and sampled"
echo "Run scripts/build_verified_release.sh for the full publication theorem"
