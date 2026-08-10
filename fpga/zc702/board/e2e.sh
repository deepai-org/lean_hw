#!/bin/bash
# e2e.sh -- the full NetBSD-on-fabric demo, end to end, as a FAIL-CLOSED
# regression. Identity is enforced before boot (guest text+data hex, bitstream,
# and debug map must match the accounted digests in e2e_manifest.env), every
# stage propagates its failure, and the script exits non-zero with `RESULT
# FAIL -- <reason>` on any deviation, or `RESULT PASS` only when boot, DOMAINS,
# ping 4/4, and both gated telnet replies (uname + echo, each byte crossing the
# §17 write gate via the shmif driver in domain 2) all succeed on the accounted
# bitstream. The `RESULT PASS` line is what scripts/check_stale.sh consumes.
# Deployed by board_sync.sh; the manifest travels with it.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/board_env.sh"
cd "$LOOM_BOARD_ROOT"

fail() { echo "RESULT FAIL -- $*" >&2; exit 1; }

# --- accounted identity: expected digests, fail-closed -----------------------
# The manifest is the identity record; env vars override individual entries.
MANIFEST="${E2E_MANIFEST:-$LOOM_BOARD_TEST_DIR/e2e_manifest.env}"
[ -f "$MANIFEST" ] || fail "identity manifest missing: $MANIFEST"
# shellcheck disable=SC1090
source "$MANIFEST"
: "${E2E_EXPECT_GUEST_TEXT:?E2E_EXPECT_GUEST_TEXT unset (guest text hex md5)}"
: "${E2E_EXPECT_GUEST_DATA:?E2E_EXPECT_GUEST_DATA unset (guest data hex md5)}"
: "${E2E_EXPECT_GUEST_TEXT_BIN:?E2E_EXPECT_GUEST_TEXT_BIN unset (guest text bin md5)}"
: "${E2E_EXPECT_GUEST_DATA_BIN:?E2E_EXPECT_GUEST_DATA_BIN unset (guest data bin md5)}"
: "${E2E_EXPECT_BIT:?E2E_EXPECT_BIT unset (bitstream md5)}"
: "${E2E_EXPECT_DEBUGMAP:?E2E_EXPECT_DEBUGMAP unset (debug-map tcl md5)}"
PING_TARGET="${E2E_PING_TARGET:-10.106.0.2}"
ECHO_TOKEN="${E2E_ECHO_TOKEN:-e2e-ok-through-gate}"

GUEST_TEXT="$LOOM_BOARD_TEST_DIR/rump_shmif_telnet_text.hex"
GUEST_DATA="$LOOM_BOARD_TEST_DIR/rump_shmif_telnet_data.hex"
# The PS-DAP fastload loads the .bin (fastload.tcl); the servicer/BSCAN load the
# .hex. Both must match the accounted guest or the board could boot a stale
# image via whichever path wins -- so enforce all four.
GUEST_TEXT_BIN="$LOOM_BOARD_TEST_DIR/rump_shmif_telnet_text.bin"
GUEST_DATA_BIN="$LOOM_BOARD_TEST_DIR/rump_shmif_telnet_data.bin"
BIT="$LOOM_OXC7_DIR/out/lnp64mini_dual_top.bit"
DEBUGMAP="$LOOM_BOARD_TEST_DIR/lnp64mini_debug_map.tcl"

check_id() {
  local what="$1" path="$2" want="$3" got
  [ -f "$path" ] || fail "$what artifact missing: $path"
  got="$(md5sum "$path" | awk '{print $1}')"
  [ "$got" = "$want" ] || fail "$what identity: got $got, expected $want ($path)"
  echo "  ok  $what = $got"
}
echo "=== accounted identity ==="
check_id "guest-text"     "$GUEST_TEXT"     "$E2E_EXPECT_GUEST_TEXT"
check_id "guest-data"     "$GUEST_DATA"     "$E2E_EXPECT_GUEST_DATA"
check_id "guest-text-bin" "$GUEST_TEXT_BIN" "$E2E_EXPECT_GUEST_TEXT_BIN"
check_id "guest-data-bin" "$GUEST_DATA_BIN" "$E2E_EXPECT_GUEST_DATA_BIN"
check_id "bitstream"      "$BIT"            "$E2E_EXPECT_BIT"
check_id "debug-map"      "$DEBUGMAP"       "$E2E_EXPECT_DEBUGMAP"

export LNP64_MINI_GATE_TBL=0x913000 LNP64_MINI_CAP_TBL=0x913100
export LNP64_CORE1_ENTRY=0x8cae00 LNP64_CORE1_STACK=0x1700000

echo "=== power cycle for a clean path ==="
bash "$LOOM_BOARD_TEST_DIR/power_cycle.sh" >"$LOOM_BOARD_STATE_DIR/power_cycle_e2e.log" 2>&1 \
  || fail "power_cycle.sh failed (see power_cycle_e2e.log)"
sleep 5

echo "=== boot the dual core ==="
touch "$LOOM_STOP_FILE"; pkill -x xsdb 2>/dev/null || true; sleep 4
rm -f "$LOOM_STOP_FILE" "$LOOM_SERVICER_LOG"
BOOT_LOG="$LOOM_BOARD_STATE_DIR/boot_e2e.log"
( "$LOOM_BOARD_TEST_DIR/boot_gem_dual_smp.sh" >"$BOOT_LOG" 2>&1 ) &
boot_pid=$!

echo "=== wait for DOMAINS (<=5 min) ==="
domains=0
for _ in $(seq 1 20); do
  sleep 15
  if grep -qa "DOMAINS: core0 cap_tbl_base" "$LOOM_SERVICER_LOG" 2>/dev/null; then
    domains=1; break
  fi
  if ! kill -0 "$boot_pid" 2>/dev/null; then
    # boot chain exited before DOMAINS: surface its cause
    if grep -qa "FPGA PROGRAM FAILED" "$BOOT_LOG" 2>/dev/null; then
      fail "bitstream programming failed (see boot_e2e.log)"
    fi
    fail "boot chain exited before DOMAINS (see boot_e2e.log)"
  fi
done
[ "$domains" = 1 ] || fail "DOMAINS never appeared within 5 min (see smp_servicer.log)"
if grep -qaE "panic|HWTRAP" "$LOOM_SERVICER_LOG" 2>/dev/null; then
  fail "panic/HWTRAP in servicer log: $(grep -aE 'panic|HWTRAP' "$LOOM_SERVICER_LOG" | tail -1)"
fi
grep -qa "CORE1:" "$LOOM_SERVICER_LOG" 2>/dev/null || fail "core1 never reported status"
echo "  DOMAINS + CORE1 established"
grep -aE "DOMAINS|CORE1" "$LOOM_SERVICER_LOG" | tail -3

echo "=== start the shmif ring pump (separate xsdb; needs the servicer bridge) ==="
# The trap servicer delegates ring R/W to a dedicated xsdb (Tcl sockets wedge
# the servicing interpreter). Without it the shmif ring never moves and the
# guest is unreachable, so this is part of bringing the demo up -- not optional.
pkill -f "[r]ing_pump" 2>/dev/null || true; sleep 1
PUMP_LOG="$LOOM_BOARD_STATE_DIR/ring_pump.log"
setsid xsdb "$LOOM_BOARD_TEST_DIR/ring_pump.tcl" >"$PUMP_LOG" 2>&1 </dev/null &
disown 2>/dev/null || true
sleep 18
[ "$(pgrep -f '[r]ing_pump' | wc -l)" -ge 1 ] || fail "ring pump did not stay up (see ring_pump.log)"
grep -qa "PUMP: connected" "$PUMP_LOG" || fail "ring pump never connected to the servicer bridge (see ring_pump.log)"
echo "  ring pump connected"

echo "=== let rump + shmif come up (90s) ==="; sleep 90

echo "=== ping over GEM0 (want 4/4) ==="
ping_out="$(ping -c 4 -W 4 "$PING_TARGET" 2>&1 || true)"
recv="$(printf '%s\n' "$ping_out" | sed -n 's/.* \([0-9]\+\) received.*/\1/p')"
recv="${recv:-0}"
echo "  received=$recv/4"
[ "$recv" -ge 4 ] || fail "ping $recv/4 to $PING_TARGET"

echo "=== telnet: uname + echo through the write gate (shmif/domain-2) ==="
tel_out="$( (sleep 8; printf 'uname\r\n'; sleep 24; printf 'echo %s\r\n' "$ECHO_TOKEN"; sleep 24) \
  | timeout 100 nc "$PING_TARGET" 23 2>&1 | tr -d '\0' || true )"
printf '%s\n' "$tel_out" | grep -aE 'micro-shell|NetBSD|'"$ECHO_TOKEN" | head -6 || true
printf '%s\n' "$tel_out" | grep -qa 'NetBSD' \
  || fail "no uname/NetBSD reply through the gate (shmif/domain-2 path)"
printf '%s\n' "$tel_out" | grep -qa "$ECHO_TOKEN" \
  || fail "no gated echo reply ($ECHO_TOKEN) -- write gate/domain-2 not proven"

echo "RESULT PASS"
