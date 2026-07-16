#!/usr/bin/env bash
# Generate and kernel-check batched concrete-SSA render witnesses.
set -euo pipefail

target=${1:-}
jobs=${2:-8}

case "$target" in
  acc8)
    rtl=rtl/acc8.v
    artifact=Acc8
    ;;
  lnp64u)
    rtl=rtl/lnp64u.v
    artifact=Lnp64u
    ;;
  *)
    echo "usage: scripts/build_release_witness.sh {acc8|lnp64u} [jobs]" >&2
    exit 2
    ;;
esac

lake exe emit "$target"

src="GeneratedRelease/$artifact"
lib=".lake/build/lib/lean/GeneratedRelease/$artifact"
python3 scripts/gen_release_witness.py "$rtl" "$src/Root.lean" \
  --block-size 128 --batch-blocks 4
mkdir -p "$lib"

compile_batch() {
  local source=$1
  local stem=${source%.lean}
  local output=".lake/build/lib/lean/$stem.olean"
  if [[ -f "$output" && ! "$source" -nt "$output" ]]; then
    return
  fi
  lake env lean "$source" -o "$output"
}
export -f compile_batch

find "$src" -maxdepth 1 -name 'Batch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _

lake env lean "$src/Root.lean" -o "$lib/Root.olean"
echo "$artifact render-witness modules kernel-checked"
