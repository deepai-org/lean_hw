#!/bin/bash
# e2e.sh -- the DEFAULT NetBSD-on-fabric regression: native GEM0, JTAG-FREE,
# DUAL-CORE SMP.
#
# Both fabric cores run one NetBSD kernel (LNP64_SMP + 2 rump vCPUs; core 1
# enters at lnp64_core1_entry). The soft cores drive the PS GEM0 MAC directly
# (in-guest GEM pump over the GP aperture); JTAG only loads the image and then
# EXITS. There is NO ring pump,
# NO host bridge, NO JTAG and NO A9 in the packet path -- real line-rate Ethernet
# (~300ms RTT) instead of the ~2.8s JTAG-pumped shmif ring. The legacy
# shmif-over-JTAG-ring path (ring_pump.tcl / shmif_bridge.py, LEGACY.md) is kept
# for debugging but is no longer the mission path.
#
# Fail-closed: enforce image/bitstream/roots identity, then boot -> DOMAINS ->
# ping 4/4 -> STOP THE SERVICER (prove JTAG-free) -> telnet `uname` + gated
# `echo` over GEM0 (each reply byte crossing the §17 write gate). `RESULT PASS`
# only if every stage holds; any deviation is `RESULT FAIL -- <reason>`.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/board_env.sh"
cd "$LOOM_BOARD_ROOT"

fail() { echo "RESULT FAIL -- $*" >&2; exit 1; }

# --- accounted identity, fail-closed ----------------------------------------
MANIFEST="${E2E_MANIFEST:-$LOOM_BOARD_TEST_DIR/e2e_manifest.env}"
[ -f "$MANIFEST" ] || fail "identity manifest missing: $MANIFEST"
# shellcheck disable=SC1090
source "$MANIFEST"
: "${E2E_EXPECT_GUEST_TEXT:?}"; : "${E2E_EXPECT_GUEST_DATA:?}"
: "${E2E_EXPECT_GUEST_TEXT_BIN:?}"; : "${E2E_EXPECT_GUEST_DATA_BIN:?}"
: "${E2E_EXPECT_BIT:?}"; : "${E2E_EXPECT_DEBUGMAP:?}"
PING_TARGET="${E2E_PING_TARGET:-10.106.0.2}"
ECHO_TOKEN="${E2E_ECHO_TOKEN:-e2e-ok-over-gem}"
ROOTS="$LOOM_BOARD_TEST_DIR/mini_domains.env"

check_id() {
  local what="$1" path="$2" want="$3" got
  [ -f "$path" ] || fail "$what artifact missing: $path"
  got="$(md5sum "$path" | awk '{print $1}')"
  [ "$got" = "$want" ] || fail "$what identity: got $got, expected $want ($path)"
  echo "  ok  $what = $got"
}
echo "=== accounted identity ==="
check_id "guest-text"     "$LOOM_BOARD_TEST_DIR/rump_shmif_telnet_text.hex" "$E2E_EXPECT_GUEST_TEXT"
check_id "guest-data"     "$LOOM_BOARD_TEST_DIR/rump_shmif_telnet_data.hex" "$E2E_EXPECT_GUEST_DATA"
check_id "guest-text-bin" "$LOOM_BOARD_TEST_DIR/rump_shmif_telnet_text.bin" "$E2E_EXPECT_GUEST_TEXT_BIN"
check_id "guest-data-bin" "$LOOM_BOARD_TEST_DIR/rump_shmif_telnet_data.bin" "$E2E_EXPECT_GUEST_DATA_BIN"
check_id "bitstream"      "$LOOM_OXC7_DIR/out/lnp64mini_dual_top.bit"       "$E2E_EXPECT_BIT"
check_id "debug-map"      "$LOOM_BOARD_TEST_DIR/lnp64mini_debug_map.tcl"    "$E2E_EXPECT_DEBUGMAP"
# The §17 gate/cap roots are nm-derived per image; a hardcoded value silently
# reads an empty gate table -> every gated write is -MALFORMED (the telnet-reply
# bug). Require the image-derived roots file to be present.
[ -f "$ROOTS" ] || fail "gate/cap roots missing: $ROOTS (build_rump_shmif_image.py emits mini_domains.env; deploy it)"
echo "  ok  roots = $(tr '\n' ' ' <"$ROOTS")"

# All image-derived params -- gate/cap roots AND the core-1 entry -- come from
# mini_domains.env (boot_gem_dual_smp sources it). Do NOT hardcode any of them:
# the SMP image links its tables and lnp64_core1_entry at per-image addresses.
# power_cycle FIRST: the PS GP path degrades per session and the GP aperture must
# start fresh (gem-mmio-aperture doctrine).

echo "=== power cycle (fresh PS GP for the GEM aperture) ==="
bash "$LOOM_BOARD_TEST_DIR/power_cycle.sh" >"$LOOM_BOARD_STATE_DIR/power_cycle_e2e.log" 2>&1 \
  || fail "power_cycle.sh failed (see power_cycle_e2e.log)"
sleep 5

echo "=== boot native-GEM guest (core0 only, JTAG loads then exits) ==="
rm -f "$LOOM_SERVICER_LOG"
BOOT_LOG="$LOOM_BOARD_STATE_DIR/boot_e2e.log"
( "$LOOM_BOARD_TEST_DIR/boot_gem_dual_smp.sh" >"$BOOT_LOG" 2>&1 ) &
boot_pid=$!

echo "=== wait for DOMAINS (<=5 min) ==="
domains=0
for _ in $(seq 1 20); do
  sleep 15
  if grep -qa "DOMAINS: core0 cap_tbl_base" "$LOOM_SERVICER_LOG" 2>/dev/null; then domains=1; break; fi
  if ! kill -0 "$boot_pid" 2>/dev/null; then
    grep -qa "FPGA PROGRAM FAILED" "$BOOT_LOG" 2>/dev/null && fail "bitstream programming failed (see boot_e2e.log)"
    fail "boot chain exited before DOMAINS (see boot_e2e.log)"
  fi
done
[ "$domains" = 1 ] || fail "DOMAINS never appeared within 5 min"
grep -qa "image roots:" "$BOOT_LOG" || fail "boot did not source the nm-derived roots (mini_domains.env)"
if grep -qaE "panic|HWTRAP" "$LOOM_SERVICER_LOG" 2>/dev/null; then
  fail "panic/HWTRAP: $(grep -aE 'panic|HWTRAP' "$LOOM_SERVICER_LOG" | tail -1)"
fi
echo "  DOMAINS established with nm-derived roots"

# Dual-core SMP: the GEM image is built LNP64_SMP + 2 rump vCPUs, so core 1
# enters the kernel at lnp64_core1_entry (from mini_domains.env). Require it to
# start and to not fault.
grep -qa "CORE1: started" "$LOOM_SERVICER_LOG" 2>/dev/null \
  || fail "core 1 never started -- SMP guest did not bring up the second hardware core"
echo "  core 1 started: $(grep -aE 'CORE1: started' "$LOOM_SERVICER_LOG" | tail -1)"

echo "=== let rump + GEM0 link come up (40s) ==="; sleep 40

echo "=== STOP the servicer -- prove JTAG-free (no xsdb in the packet path) ==="
touch "$LOOM_STOP_FILE"; sleep 5
[ "$(pgrep -x xsdb | wc -l)" -eq 0 ] || fail "servicer xsdb did not exit; not JTAG-free"
echo "  servicer stopped (xsdb=0); guest runs native GEM0 autonomously"

echo "=== ping over GEM0 (want 4/4), JTAG dead ==="
ping_out="$(ping -c 4 -W 4 "$PING_TARGET" 2>&1 || true)"
recv="$(printf '%s\n' "$ping_out" | sed -n 's/.* \([0-9]\+\) received.*/\1/p')"; recv="${recv:-0}"
echo "  received=$recv/4"
[ "$recv" -ge 4 ] || fail "ping $recv/4 to $PING_TARGET over GEM0"

echo "=== telnet: uname + gated echo over GEM0 (each byte crosses the §17 gate) ==="
tel_out="$( { printf 'uname\r\n'; sleep 3; printf 'echo %s\r\n' "$ECHO_TOKEN"; sleep 3; printf 'exit\r\n'; } \
  | timeout 25 nc -w 18 "$PING_TARGET" 23 2>&1 | tr -d '\0' || true )"
printf '%s\n' "$tel_out" | grep -aE 'micro-shell|NetBSD|'"$ECHO_TOKEN" | head -6 || true
printf '%s\n' "$tel_out" | grep -qa 'NetBSD' || fail "no uname/NetBSD reply through the gate over GEM0"
printf '%s\n' "$tel_out" | grep -qa "$ECHO_TOKEN" || fail "no gated echo reply ($ECHO_TOKEN) -- §17 write gate not proven"

echo "RESULT PASS"
