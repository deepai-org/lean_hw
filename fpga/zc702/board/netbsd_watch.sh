#!/bin/bash
# netbsd_watch.sh -- keep the fabric guest alive (§65 autonomy, liveness half).
# The service brings the board up; this notices when it goes down. Three
# consecutive misses (~90 s) trigger one unattended recovery, rate-limited so a
# genuinely broken board is not power-cycled in a loop.
set -u
GUEST=10.106.0.2
IF=zc702fpga0
LOG=/home/kevin/autonomy/watch.log
STAMP=/tmp/netbsd_watch_last_restart
COOLDOWN=1800          # seconds between recoveries
say() { echo "[$(date +%F' '%T)] $*" >> "$LOG"; }

miss=0
for i in 1 2 3; do
  timeout 3 ping -I "$IF" -c1 -W1 "$GUEST" >/dev/null 2>&1 || miss=$((miss+1))
  [ $i -lt 3 ] && sleep 20
done
[ "$miss" -lt 3 ] && exit 0

now=$(date +%s)
last=$(cat "$STAMP" 2>/dev/null || echo 0)
if [ $((now - last)) -lt "$COOLDOWN" ]; then
  say "guest down, but a recovery ran $((now-last))s ago (<${COOLDOWN}s) -- holding off"
  exit 0
fi
echo "$now" > "$STAMP"
say "guest unreachable on 3/3 probes -- triggering netbsd-fabric recovery"
systemctl restart --no-block netbsd-fabric.service
