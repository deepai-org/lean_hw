#!/usr/bin/env bash
# Generate and kernel-check batched concrete-SSA render witnesses.
set -euo pipefail

# The generated compositional elaborators recurse over the concrete source
# action tree. Their proof terms are shared through named declarations, but
# the meta-level traversal itself can exceed the small default process stack.
ulimit -s unlimited

target=${1:-}
jobs=${2:-8}
mode=${3:-full}

if [[ "$mode" != full && "$mode" != sample ]]; then
  echo "mode must be 'full' or 'sample'" >&2
  exit 2
fi

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
    design_imports=(Machines.Lnp64u.Hw.Core Machines.Lnp64u.Hw.Demo
      Machines.Lnp64u.Theorems.ReleaseOrder)
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

# Generated modules are compiled directly with `lean`, outside Lake's module
# graph. Build every import supplied to the generator, plus its shared
# certificate engines, so a clean checkout cannot rely on stale `.olean`s.
lake build Loom.Release.SymbolicCertificate Loom.Release.SymbolicDecide \
  Tools.ReleaseCertGen "${design_imports[@]}"

find "$src" -maxdepth 1 -name 'Batch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _

lake env lean "$(realpath "$src/Root.lean")" -o "$lib/Root.olean"

lake env lean --run "$(realpath "$src/CertGen.lean")"

# Generated correctness is kernel-checked below; this repeated generation is
# solely the clean-clone reproducibility gate. Hashes detect drift between the
# two runs and are not used to bind or certify the RTL bytes.
generated_digest=$(python3 scripts/generated_tree_digest.py "$src")
python3 scripts/gen_release_witness.py "${generator_args[@]}"
lake env lean --run "$(realpath "$src/CertGen.lean")"
regenerated_digest=$(python3 scripts/generated_tree_digest.py "$src")
if [[ "$generated_digest" != "$regenerated_digest" ]]; then
  echo "$artifact release source generation is nondeterministic" >&2
  exit 1
fi
echo "$artifact generated release sources are deterministic"

find "$src" -maxdepth 1 -name 'IndexedCertBatch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _
find "$src" -maxdepth 1 -name 'IndexedPortCertBatch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _

find "$src" -maxdepth 1 -name 'SemanticWireBatch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _
lake env lean "$(realpath "$src/SemanticWires.lean")" -o "$lib/SemanticWires.olean"

if [[ "$mode" == sample ]]; then
  if [[ "$target" != lnp64u ]]; then
    echo "sample mode is defined only for the large LNP64-u artifact" >&2
    exit 2
  fi
  sample_sources=()
  for index in 0 206 412 618 824; do
    sample_sources+=("$src/SemanticRegBatch$index.lean")
  done
  printf '%s\0' "${sample_sources[@]}" | \
    xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _
  echo "Lnp64u REVIEW SAMPLE passed: exact bytes, all wire certificates, and register leaves 0,206,412,618,824"
  echo "This is not the full LNP64-u release theorem; use scripts/build_verified_release.sh for Tier A"
  exit 0
fi

find "$src" -maxdepth 1 -name 'SemanticRegBatch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _
lake env lean "$(realpath "$src/SemanticRegs.lean")" -o "$lib/SemanticRegs.olean"
find "$src" -maxdepth 1 -name 'ReadRegBatch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _
lake env lean "$(realpath "$src/ReadRegs.lean")" -o "$lib/ReadRegs.olean"
find "$src" -maxdepth 1 -name 'DeclMemBatch*.lean' -print0 | sort -z | \
  xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _
lake env lean "$(realpath "$src/DeclMems.lean")" -o "$lib/DeclMems.olean"
lake env lean "$(realpath "$src/SemanticActions.lean")" -o "$lib/SemanticActions.olean"
if [[ -f "$src/SemanticDesignWF.lean" ]]; then
  lake env lean "$(realpath "$src/SemanticDesignWF.lean")" \
    -o "$lib/SemanticDesignWF.olean"
fi
lake env lean "$(realpath "$src/SemanticReads.lean")" -o "$lib/SemanticReads.olean"
lake env lean "$(realpath "$src/SemanticMems.lean")" -o "$lib/SemanticMems.olean"
lake env lean "$(realpath "$src/SemanticModule.lean")" -o "$lib/SemanticModule.olean"
if [[ -f "$src/SemanticRelease.lean" ]]; then
  lake env lean "$(realpath "$src/SemanticRelease.lean")" \
    -o "$lib/SemanticRelease.olean"
fi
echo "$artifact render and semantic certificate modules kernel-checked"
