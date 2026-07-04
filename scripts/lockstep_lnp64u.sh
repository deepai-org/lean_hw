#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0
# Corroborate the emitted LNP64-µ µVerilog against the ISS (task 1.11).
# Emits the core + a generated ISS-golden testbench, simulates 2000 cycles
# with iverilog, checks the goldens, then runs yosys synth for
# synthesis-cleanliness. Standalone (NOT in ci.sh: the emitted core is
# large — see Machines/Lnp64u/Hw/DESIGN.md).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== emit (lake exe emit lnp64u)"
time lake exe emit lnp64u
ls -l rtl/lnp64u.v rtl/tb_lnp64u.v

echo "== iverilog compile"
time iverilog -g2012 -o rtl/lnp64u.vvp rtl/lnp64u.v rtl/tb_lnp64u.v

echo "== simulate (2000 cycles)"
time vvp rtl/lnp64u.vvp | tee rtl/lnp64u_sim.log
grep -q "LNP64U: PASS" rtl/lnp64u_sim.log

echo "== yosys synth"
# Memory-aware flow: the plain generic `synth` FF-maps the 4096x32 RAM
# (131k DFFs + full read-mux trees) and then abc needs >60 GB. Keep the
# RAM as one $mem cell (`memory -nomap`, the BRAM it would become on any
# real target) and gate-map the logic with abc -fast.
# (`-q` silences stdout but `-l` still writes the full log, `stat` included.)
time yosys -q -l rtl/lnp64u_yosys.log -p "read_verilog rtl/lnp64u.v; \
  hierarchy -top lnp64u; proc; opt; memory -nomap; opt -full; techmap; \
  opt; abc -fast; opt_clean; stat"
grep -A 40 "=== lnp64u ===" rtl/lnp64u_yosys.log | tail -42 || tail -40 rtl/lnp64u_yosys.log

echo "lockstep_lnp64u: OK (RTL matches ISS goldens; yosys synth clean)"
