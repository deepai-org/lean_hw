#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Push fpga/zc702/board/ to the board host, and VERIFY it landed.
#
# This repository is the source of truth for the board layer
# (`REPO_BOUNDARY.md`). This script verifies every deployed file after copying.
#
#   scripts/board_sync.sh          # push and verify
#   scripts/board_sync.sh --check  # verify only; non-zero if the host differs
set -uo pipefail
cd "$(dirname "$0")/.."
: "${BOARD:?set BOARD to the SSH host, for example user@board-host}"
BOARD_ROOT=${BOARD_ROOT:-substrate0}
DEST=${DEST:-$BOARD_ROOT/test}
if [ -n "${BOARD_PW:-}" ]; then
  command -v sshpass >/dev/null || { echo "board_sync: BOARD_PW set but sshpass is unavailable"; exit 2; }
  SSH=(sshpass -p "$BOARD_PW" ssh -o StrictHostKeyChecking=no "$BOARD")
  SCP=(sshpass -p "$BOARD_PW" scp -o StrictHostKeyChecking=no)
else
  SSH=(ssh "$BOARD")
  SCP=(scp)
fi
CHECK_ONLY=0; [ "${1:-}" = "--check" ] && CHECK_ONLY=1
FAIL=0
# Most of the board layer lives in $DEST (substrate0/test). A few files belong
# elsewhere on the host and are mapped here rather than being filed in the
# wrong directory to suit the loop -- the build script has to sit next to the
# chipdb it references.
dest_for() {
  case "$1" in
    build_oxc7_seed.sh) echo "$BOARD_ROOT/oxc7" ;;
    *)                  echo "$DEST" ;;
  esac
}

for f in fpga/zc702/board/*; do
  b=$(basename "$f")
  [ -f "$f" ] || continue
  D=$(dest_for "$b")
  if [ "$CHECK_ONLY" = 0 ]; then "${SCP[@]}" "$f" "$BOARD:$D/$b" >/dev/null 2>&1; fi
  want=$(md5sum < "$f" | cut -d' ' -f1)
  got=$("${SSH[@]}" "md5sum < $D/$b 2>/dev/null" | cut -d' ' -f1)
  if [ "$want" = "$got" ]; then printf '  ok     %s\n' "$b"
  else printf '  DIFFER %s (repo %s, host %s)\n' "$b" "${want:0:8}" "${got:0:8}"; FAIL=1; fi
done
[ "$FAIL" = 0 ] && echo "board_sync: OK — the host matches this repo" \
                || echo "board_sync: FAILED — the host does not match; do NOT trust a run from it"
exit "$FAIL"
