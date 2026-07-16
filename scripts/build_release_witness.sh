#!/usr/bin/env bash
# Generate and kernel-check batched concrete-SSA render witnesses.
set -euo pipefail

target=${1:-}
jobs=${2:-8}

case "$target" in
  acc8)
    rtl=rtl/acc8.v
    artifact=Acc8
    design_expr='Machines.Acc8.Core.design (Machines.Acc8.loadProg Machines.Acc8.golden)'
    design_imports=(Machines.Acc8.Core Machines.Acc8.Iss)
    ;;
  lnp64u)
    rtl=rtl/lnp64u.v
    artifact=Lnp64u
    design_expr='Machines.Lnp64u.Hw.core Machines.Lnp64u.Demo.sysManifest'
    design_imports=(Machines.Lnp64u.Hw.Core Machines.Lnp64u.Hw.Demo)
    ;;
  *)
    echo "usage: scripts/build_release_witness.sh {acc8|lnp64u} [jobs]" >&2
    exit 2
    ;;
esac

lake exe emit "$target"

src="GeneratedRelease/$artifact"
lib=".lake/build/lib/lean/GeneratedRelease/$artifact"
generator_args=("$rtl" "$src/Root.lean" --block-size 128 --batch-blocks 4
  --design-expr "$design_expr")
for module in "${design_imports[@]}"; do
  generator_args+=(--design-import "$module")
done
python3 scripts/gen_release_witness.py "${generator_args[@]}"
python3 scripts/check_release_binding.py "$rtl" "$src"
mkdir -p "$lib"

compile_batch() {
  local source=$1
  local stem=${source%.lean}
  local output=".lake/build/lib/lean/$stem.olean"
  if [[ -f "$output" && ! "$source" -nt "$output" ]]; then
    return
  fi
  lake env lean "$(realpath "$source")" -o "$output"
}
export -f compile_batch

find "$src" -maxdepth 1 -name 'Batch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _

lake env lean "$(realpath "$src/Root.lean")" -o "$lib/Root.olean"
lake env lean --run "$(realpath "$src/CertGen.lean")"

find "$src" -maxdepth 1 -name 'CertBatch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _

lake env lean "$(realpath "$src/CertData.lean")" -o "$lib/CertData.olean"
echo "$artifact render and semantic certificate modules kernel-checked"
