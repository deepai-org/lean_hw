# Legacy: shmif-over-JTAG-ring network path

The mission network path is now **native GEM0** (`e2e.sh`): the soft core drives
the PS GEM0 MAC directly over the GP aperture, JTAG loads the image then exits,
and there is no JTAG or A9 in the packet path. See `e2e.sh` and
[[gem-mmio-aperture]].

These files implement the **superseded** shmif-over-JTAG-ring path, where every
packet was moved over the BSCAN chain by a host-side pump+bridge (~2.8s RTT):

- `ring_pump.tcl` — dedicated xsdb that R/W's the shmif ring over JTAG.
- `shmif_bridge.py` / `start_bridge.sh` / `start_pump.sh` — host tap<->ring
  bridge (board-only; needs sudo + a shmif0 tap; collides with the GEM demo's
  use of 10.106.0.0/24).

They are kept for debugging a guest whose GEM driver is not up, and for the
emulator watch-seam path. They are NOT the accepted mission path. Do not add new
work on the JTAG ring — put it on native GEM0.

## Legacy fixtures (frozen to old images)

- `boot_smp_igfall.sh` — from the closed §70/§74 ig_fall / fault-cause-latch
  investigation, pinned to a specific old image (`a23acd8e`) on the CAUSE-LATCH
  bitstream. Its gate/cap roots and core-1 entry are hardcoded to THAT image and
  are NOT nm-derived. The live fault-record read is now `read_frozen.tcl`. Do not
  run it against the current image.

The stale board-only `smp_image.env` (a pre-`mini_domains.env` root file) has
been removed; all maintained boots derive roots from `mini_domains.env`.
