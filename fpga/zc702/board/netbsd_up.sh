#!/bin/bash
# netbsd_up.sh -- §65 power-on autonomy: power-off board -> NetBSD serving
# native GEM0 on the dual-core Loom SoC, unattended, no DIP changes.
#
# One entry point, safe to run from systemd (netbsd-fabric.service), cron,
# or by hand. Every step retries once through the known JTAG-wedge recovery
# (pkill the stack + power cycle). Evidence is stored under the configured
# board-state directory.
# (full log, servicer tail, camera snapshot, STATUS file).
#
# Image parameters come from the deployed `smp_image.env` (written at image deploy
# time), so an image update never requires editing this script.
set -u
source "$(dirname "${BASH_SOURCE[0]}")/board_env.sh"
TS=$(date +%Y%m%d-%H%M%S)
EV="$LOOM_BOARD_STATE_DIR/autonomy/$TS"
mkdir -p "$EV"
L=$EV/run.log
exec >> "$L" 2>&1
cd "$LOOM_BOARD_ROOT"
say() { echo "[$(date +%H:%M:%S)] $*"; }
fail() { say "FAIL: $*"; echo "FAIL $*" > "$EV/STATUS"; exit 1; }

[ -f "$LOOM_BOARD_TEST_DIR/smp_image.env" ] && . "$LOOM_BOARD_TEST_DIR/smp_image.env"
export LNP64_CORE1_ENTRY="${LNP64_CORE1_ENTRY:-0x8ca100}"
export LNP64_CORE1_STACK="${LNP64_CORE1_STACK:-0x01700000}"
export LNP64_MMU="${LNP64_MMU:-0}"
export LNP64_RELOC="${LNP64_RELOC:-0}"   # EXT-7 stage B: non-identity translation
# §17 protection domains: the gate/cap table roots the servicer pokes as
# cmd 74/75. Empty = no tables installed = every gate/cap walk fails closed
# (a domainless image boots exactly as before). The gate walk addresses DDR
# untranslated, so domains require the identity map (LNP64_RELOC must stay 0).
export LNP64_MINI_GATE_TBL="${LNP64_MINI_GATE_TBL:-}"
export LNP64_MINI_CAP_TBL="${LNP64_MINI_CAP_TBL:-}"

say "== netbsd_up: power-off -> NetBSD (dual SMP, core1 entry $LNP64_CORE1_ENTRY) =="
for attempt in 1 2; do
  say "== attempt $attempt: clear JTAG stack + power cycle =="
  pkill -9 -x xsdb 2>/dev/null; pkill -9 -f "lnp64 trap-server" 2>/dev/null
  pkill -9 -f "loader -exec hw_server" 2>/dev/null; pkill -9 -f "unwrapped.*hw_server" 2>/dev/null
  sleep 3
  bash "$LOOM_BOARD_TEST_DIR/power_cycle.sh" > "$EV/power_cycle.$attempt.log" 2>&1
  grep -q POWER_CYCLE_OK "$EV/power_cycle.$attempt.log" && break
  say "power_cycle attempt $attempt failed"
  [ "$attempt" = 2 ] && fail "power_cycle (see power_cycle.*.log)"
done
say "PS up, DDR verified"

say "== boot (program dual bit + fastload + dual servicer) =="
mkdir -p /tmp/rumpns /tmp/rumpns2
rm -f "$LOOM_STOP_FILE"
setsid nohup bash "$LOOM_BOARD_TEST_DIR/boot_gem_dual_smp.sh" \
  > "$EV/boot.log" 2>&1 < /dev/null &
BOOTPID=$!

say "== wait for native GEM0 (up to 20 min) =="
UP=0
for i in $(seq 1 120); do
  if timeout 3 ping -I zc702fpga0 -c1 -W1 10.106.0.2 >/dev/null 2>&1; then UP=1; break; fi
  kill -0 "$BOOTPID" 2>/dev/null || say "note: boot script exited (servicer may still run)"
  sleep 10
done
[ "$UP" = 1 ] || fail "no GEM ping after 20 min (see boot.log and $LOOM_SERVICER_LOG)"
say "GEM up after ~$((i*10))s"

say "== verify: ping + telnet banner =="
ping -I zc702fpga0 -c 5 10.106.0.2 | tail -2
( sleep 0.3; printf "uname\r\n"; sleep 3 ) | timeout 10 telnet 10.106.0.2 2>/dev/null \
  | tr -d '\r' | grep -a "NetBSD" || say "warn: telnet banner not captured (non-fatal)"

say "== quiesce: stop servicer -> zero-BSCAN steady state =="
touch "$LOOM_STOP_FILE"
sleep 10
tail -5 "$LOOM_SERVICER_LOG" > "$EV/servicer_tail.log" 2>/dev/null
pkill -9 -x xsdb 2>/dev/null; pkill -9 -f "lnp64 trap-server" 2>/dev/null
sleep 2

say "== final acceptance: ping with BSCAN quiet =="
PF=$(ping -I zc702fpga0 -c 10 10.106.0.2 | tail -2)
echo "$PF"
echo "$PF" | grep -q " 0% packet loss" || fail "packet loss after servicer stop"

ffmpeg -y -f v4l2 -input_format mjpeg -video_size 2592x1944 -i /dev/video0 \
  -frames:v 5 -update 1 "$EV/board.jpg" >/dev/null 2>&1 && say "camera evidence saved"
say "== PASS: NetBSD serving native GEM0, dual-core, BSCAN quiet =="
{ echo "PASS $TS"; echo "core1_entry=$LNP64_CORE1_ENTRY"; echo "$PF"; } > "$EV/STATUS"
