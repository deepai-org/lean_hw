#!/usr/bin/env bash
# Copyright (c) 2026 Kevin Baragona
# SPDX-License-Identifier: Apache-2.0 OR SHL-2.1
# Shared board-host configuration. Override any value in the environment.

# Board-local, machine-specific values (Vivado location, etc.) live OUTSIDE the
# repo so the tree stays path-free and portable. Each board provides its own at
# ~/.config/loom-board.env (git-ignored, not synced) -- e.g.
#   export LOOM_VIVADO_BIN=/opt/Xilinx/2025.2/Vivado/bin
# Sourced first so its exports win over the defaults below.
LOOM_BOARD_LOCAL_ENV=${LOOM_BOARD_LOCAL_ENV:-$HOME/.config/loom-board.env}
[ -f "$LOOM_BOARD_LOCAL_ENV" ] && . "$LOOM_BOARD_LOCAL_ENV"

LOOM_BOARD_TEST_DIR=${LOOM_BOARD_TEST_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}
LOOM_BOARD_ROOT=${LOOM_BOARD_ROOT:-$(cd "$LOOM_BOARD_TEST_DIR/.." && pwd)}
LOOM_OXC7_DIR=${LOOM_OXC7_DIR:-$LOOM_BOARD_ROOT/oxc7}
LNP64_ROOT=${LNP64_ROOT:-$LOOM_BOARD_ROOT/lnp64}
LOOM_BOARD_STATE_DIR=${LOOM_BOARD_STATE_DIR:-$LOOM_BOARD_ROOT/board-state}
LOOM_VIVADO_BIN=${LOOM_VIVADO_BIN:-}
LOOM_SERVICER_LOG=${LOOM_SERVICER_LOG:-$LOOM_BOARD_STATE_DIR/smp_servicer.log}
LOOM_STOP_FILE=${LOOM_STOP_FILE:-$LOOM_BOARD_STATE_DIR/stop_servicer}

mkdir -p "$LOOM_BOARD_STATE_DIR"
export LOOM_BOARD_TEST_DIR LOOM_BOARD_ROOT LOOM_OXC7_DIR LNP64_ROOT
export LOOM_BOARD_STATE_DIR LOOM_VIVADO_BIN LOOM_SERVICER_LOG LOOM_STOP_FILE
if [ -n "$LOOM_VIVADO_BIN" ]; then
  export PATH="$LOOM_VIVADO_BIN:$PATH"
fi
