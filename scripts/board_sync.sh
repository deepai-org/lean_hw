#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
#
# Push fpga/zc702/board/ to the board host, and VERIFY it landed.
#
# The §69 incident: the board host's copies of netbsd_up.sh and
# lnp64_rump_run_dual.tcl had been edited in place and carried the entire
# EXT-7 stage-B translation block, which existed in no repo. The fix had to
# be reconstructed by reading a running machine. Then /tmp on that host was
# cleared and a backup vanished with it.
#
# So: this repo is the source of truth for the board layer (REPO_BOUNDARY.md),
# and this script is the only sanctioned way to update the host. It diffs
# after copying, because a silent scp failure looks exactly like success.
#
#   scripts/board_sync.sh          # push and verify
#   scripts/board_sync.sh --check  # verify only; non-zero if the host differs
set -uo pipefail
cd "$(dirname "$0")/.."
BOARD=${BOARD:-kevin@100.112.37.3}
DEST=${DEST:-substrate0/test}
SSH=(sshpass -p "${BOARD_PW:-deepai}" ssh -o StrictHostKeyChecking=no "$BOARD")
SCP=(sshpass -p "${BOARD_PW:-deepai}" scp -o StrictHostKeyChecking=no)
CHECK_ONLY=0; [ "${1:-}" = "--check" ] && CHECK_ONLY=1
FAIL=0
# Most of the board layer lives in $DEST (substrate0/test). A few files belong
# elsewhere on the host and are mapped here rather than being filed in the
# wrong directory to suit the loop -- the build script has to sit next to the
# chipdb it references.
dest_for() {
  case "$1" in
    build_oxc7_seed.sh) echo "substrate0/oxc7" ;;
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
