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

source "$(dirname "${BASH_SOURCE[0]}")/phase_timing.sh"
LOOM_PHASE_SCOPE="$target"
loom_phase_log_init

run_phase "emit RTL" lake exe emit "$target"

src="GeneratedRelease/$artifact"
lib=".lake/build/lib/lean/GeneratedRelease/$artifact"
block_size=128
batch_blocks=4
generator_args=("$rtl" "$src/Root.lean" --block-size "$block_size" --batch-blocks "$batch_blocks"
  --design-expr "$design_expr")
for module in "${design_imports[@]}"; do
  generator_args+=(--design-import "$module")
done
run_phase "generate witness sources" \
  python3 scripts/gen_release_witness.py "${generator_args[@]}"
run_phase "check release binding" \
  python3 scripts/check_release_binding.py "$rtl" "$src"
mkdir -p "$lib"

compile_batch() {
  local source=$1
  local stem=${source%.lean}
  local output=".lake/build/lib/lean/$stem.olean"
  local rebuild=0
  if [[ ! -f "$output" || "$source" -nt "$output" ]]; then
    rebuild=1
  else
    while read -r _ module _; do
      local dependency=".lake/build/lib/lean/${module//./\/}.olean"
      if [[ -f "$dependency" && "$dependency" -nt "$output" ]]; then
        rebuild=1
        break
      fi
    done < <(grep '^import ' "$source")
  fi
  if [[ "$rebuild" == 0 ]]; then
    return
  fi
  # Outer xargs already provides file-level parallelism.  Without this cap,
  # every Lean process also starts an internal worker pool and 30 nominal
  # jobs create roughly 60 runnable kernel threads on a 32-core machine.
  lake env lean -j 1 "$(realpath "$source")" -o "$output"
}
export -f compile_batch

# Generated modules are compiled directly with `lean`, outside Lake's module
# graph. Build every import supplied to the generator, plus its shared
# certificate engines, so a clean checkout cannot rely on stale `.olean`s.
# `release_imports` are imported by generated modules but are not design
# imports, so a clean checkout has no object for them unless they are named
# here. `SemanticRelease` in particular imports the refinement closure.
case "$target" in
  acc8)
    release_imports=(Loom.Release.SymbolicVerified
      Machines.Acc8.Theorems.AR Machines.Acc8.Theorems.AEV)
    ;;
  lnp64u)
    release_imports=(Loom.Release.SymbolicVerified
      Machines.Lnp64u.Theorems.DemoWitness Machines.Lnp64u.Theorems.RMC)
    ;;
esac

run_phase "lake prerequisites (includes R-MC closure)" \
  lake build Loom.Release.SymbolicCertificate Loom.Release.SymbolicDecide \
  Loom.Release.WholeRegisterPlan Loom.Release.ToProgram \
  Tools.ReleaseCertGen "${design_imports[@]}" "${release_imports[@]}"

# Generated modules are compiled outside Lake's module graph, so any Loom or
# Machines module they import must be built explicitly. Enumerating those by
# hand is whack-a-mole -- a clean checkout fails on whichever one was missed,
# and a warm tree hides it. Scan the generated sources instead. Lake no-ops
# when the targets are already up to date, so calling this repeatedly as more
# sources are generated is cheap.
build_external_imports() {
  local -a targets
  mapfile -t targets < <(
    grep -h '^import \(Loom\|Machines\)\.' "$src"/*.lean 2>/dev/null |
      awk '{print $2}' | sort -u)
  if ((${#targets[@]} == 0)); then
    return 0
  fi
  lake build "${targets[@]}"
}

compile_wire_owner() {
  local source=$1
  compile_batch "$source"
  local base=${source##*/}
  local owner=$((10#${base:5:3}))
  local child
  printf -v child '%s/IndexedBatch%04d.lean' "${source%/*}" "$owner"
  [[ -f "$child" ]] && compile_batch "$child"
  return 0
}
export -f compile_wire_owner

compile_glob() {
  find "$src" -maxdepth 1 -name "$1" -print0 | sort -z | \
    xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _
}

# Some generated families need several GiB per module. Running $jobs of them
# at once exhausts memory and the kernel kills the build -- SemanticWireBatch
# peaks at about 6.6 GiB per module, so 32 workers demand ~213 GiB. Cap the
# pool by measured per-module footprint instead of by core count.
compile_glob_capped() {
  local pattern=$1
  local per_job_kb=$2
  local available_kb cap
  available_kb=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo 2>/dev/null || echo 0)
  cap=$((available_kb / per_job_kb))
  ((cap < 1)) && cap=1
  ((cap > jobs)) && cap=$jobs
  echo "    ($pattern: $cap workers, ~$((per_job_kb / 1024 / 1024)) GiB each)"
  find "$src" -maxdepth 1 -name "$pattern" -print0 | sort -z | \
    xargs -0 -r -n1 -P "$cap" bash -c 'compile_batch "$1"' _
}

run_phase "generated external imports" build_external_imports

run_phase "wire batches" bash -c \
  "find '$src' -maxdepth 1 -name 'Batch*.lean' -print0 | sort -z | \
   xargs -0 -r -n1 -P $jobs bash -c 'compile_wire_owner \"\$1\"' _"

# `Root` imports the balanced composition of all wire batches.  This module is
# generated outside Lake's static graph, so compile it explicitly on a clean
# checkout instead of accidentally relying on a stale object.
run_phase "tree chunk batches" compile_glob 'TreeChunkBatch*.lean'
run_phase "indexed root" compile_batch "$src/IndexedRoot.lean"
run_phase "memory data" compile_glob 'MemData*.lean'
run_phase "memory renders" compile_glob 'MemRender*.lean'
run_phase "memory roots" compile_glob 'MemRoot*.lean'
run_phase "program data" compile_batch "$src/ProgramData.lean"
# The parsed witness must be the verified compiler's own output. This gate
# compares it against `Design.toProgram` -- the in-Lean reconstruction of the
# printer's flattening -- so a generator or printer drift fails the release
# here rather than surviving as a semantically-checked-but-different program.
case "$target" in
  acc8) parity_script=scripts/check_toprogram_acc8.lean ;;
  lnp64u) parity_script=scripts/check_toprogram_lnp64u.lean ;;
esac
run_phase "toProgram parity gate" \
  lake env lean --run "$(realpath "$parity_script")"
run_phase "framing fixed" compile_batch "$src/FramingFixed.lean"
run_phase "framing registers" compile_glob 'FramingReg*.lean'
run_phase "framing outputs" compile_glob 'FramingOut*.lean'
run_phase "render root" compile_batch "$src/Root.lean"

if [[ "$target" == lnp64u ]]; then
  # The large core uses one action-wide synthesis pass and compact per-register
  # projections.  The former CertGen path traversed the complete action tree
  # once for each of 825 registers and was the source of the multi-hour build.
  scripts/build_all_action_dag_cuts.sh "$jobs"
  run_phase "fast indexed bridge batches" compile_glob 'FastIndexedBridgeBatch*.lean'
  run_phase "fast indexed bridge" compile_batch "$src/FastIndexedBridge.lean"
  run_phase "generate hybrid rules" \
    lake exe actionwidegen lnp64u-hybrid-rules "$src/Runtime.tsv" "$src"
  run_phase "hybrid external imports" build_external_imports
  run_phase "hybrid base" compile_batch "$src/HybridBase.lean"
  run_phase "hybrid core shape" compile_batch "$src/HybridCoreShape.lean"
  for index in 000 001 002 003; do
    run_phase "hybrid rule $index" compile_batch "$src/HybridRule${index}.lean"
  done
  run_phase "hybrid prelude" compile_batch "$src/HybridPrelude.lean"
  run_phase "hybrid registers" compile_glob 'HybridReg*.lean'
  run_phase "hybrid root" compile_batch "$src/HybridRoot.lean"
  # The hybrid path replaced CertGen's register certificates but not its
  # memory-port ones, and SemanticMems still imports IndexedPortCertBatch.
  # `CertGenPorts` synthesizes only `cert.mems`, which is all
  # `indexedPortDeclarationBatchesOfMems` reads. Running full `CertGen` here
  # cost 506 s to emit one imported batch, because it also built 825 register
  # certificates and a whole-plan synthesis that nothing on this path imports;
  # the narrow entry point emits a byte-identical batch in 18 s.
  run_phase "port certificate generation" \
    lake env lean --run "$(realpath "$src/CertGenPorts.lean")"
else
  run_phase "certificate generation" \
    lake env lean --run "$(realpath "$src/CertGen.lean")"
fi

# Generated correctness is kernel-checked below. Re-run the fast structural
# source generator for the reproducibility gate, but do not repeat expensive
# certificate synthesis: certificate-generator determinism is irrelevant to
# soundness because every emitted certificate is checked by the kernel.
generated_digest=$(python3 scripts/generated_tree_digest.py "$src")
run_phase "regenerate for determinism gate" \
  python3 scripts/gen_release_witness.py "${generator_args[@]}"
regenerated_digest=$(python3 scripts/generated_tree_digest.py "$src")
if [[ "$generated_digest" != "$regenerated_digest" ]]; then
  echo "$artifact release source generation is nondeterministic" >&2
  exit 1
fi
echo "$artifact generated release sources are deterministic"

if [[ "$target" != lnp64u ]]; then
  run_phase "indexed cert batches" compile_glob 'IndexedCertBatch*.lean'
  run_phase "plan cert batches" compile_glob 'PlanCertBatch*.lean'
fi
# Memory-port certificates are needed on both paths: SemanticMems imports
# them regardless of how register certificates were produced.
run_phase "indexed port cert batches" compile_glob 'IndexedPortCertBatch*.lean'

run_phase "semantic wire batches" compile_glob_capped 'SemanticWireBatch*.lean' 7000000
run_phase "semantic wires" lake env lean \
  "$(realpath "$src/SemanticWires.lean")" -o "$lib/SemanticWires.olean"

if [[ "$mode" == sample ]]; then
  if [[ "$target" != lnp64u ]]; then
    echo "sample mode is defined only for the large LNP64-u artifact" >&2
    exit 2
  fi
  sample_sources=()
  for index in 0 206 412 618 824; do
    batch=$((index / 16))
    sample_sources+=("$src/SemanticRegBatch$batch.lean")
  done
  printf '%s\0' "${sample_sources[@]}" | \
    xargs -0 -r -n1 -P "$jobs" bash -c 'compile_batch "$1"' _
  echo "Lnp64u REVIEW SAMPLE passed: exact bytes, all wire certificates, and register leaves 0,206,412,618,824"
  echo "This is not the full LNP64-u release theorem; use scripts/build_verified_release.sh for Tier A"
  exit 0
fi

run_phase "semantic register batches" compile_glob_capped 'SemanticRegBatch*.lean' 4500000
run_phase "semantic registers" lake env lean \
  "$(realpath "$src/SemanticRegs.lean")" -o "$lib/SemanticRegs.olean"
run_phase "read register batches" compile_glob 'ReadRegBatch*.lean'
run_phase "read registers" lake env lean \
  "$(realpath "$src/ReadRegs.lean")" -o "$lib/ReadRegs.olean"
run_phase "declared memory batches" compile_glob 'DeclMemBatch*.lean'
run_phase "declared memories" lake env lean \
  "$(realpath "$src/DeclMems.lean")" -o "$lib/DeclMems.olean"
run_phase "semantic actions" lake env lean \
  "$(realpath "$src/SemanticActions.lean")" -o "$lib/SemanticActions.olean"
if [[ -f "$src/SemanticDesignWF.lean" ]]; then
  run_phase "semantic design wf" lake env lean \
    "$(realpath "$src/SemanticDesignWF.lean")" -o "$lib/SemanticDesignWF.olean"
fi
run_phase "semantic reads" lake env lean \
  "$(realpath "$src/SemanticReads.lean")" -o "$lib/SemanticReads.olean"
# Memory init blocks and write ports are independent kernel checks; the
# monolithic SemanticMems ran them serially for 832 s on one core. Each is
# now its own module so this parallelizes, and a single edit re-checks one
# block instead of the whole family (the CI-tier gate needs the worst
# single-edit class under 600 s).
run_phase "semantic memory base" compile_batch "$src/SemanticMemBase.lean"
run_phase "semantic memory init batches" compile_glob 'SemanticMemInit*.lean'
run_phase "semantic memory port batches" compile_glob 'SemanticMemPort*.lean'
run_phase "semantic memories" lake env lean \
  "$(realpath "$src/SemanticMems.lean")" -o "$lib/SemanticMems.olean"
run_phase "semantic module" lake env lean \
  "$(realpath "$src/SemanticModule.lean")" -o "$lib/SemanticModule.olean"
if [[ -f "$src/SemanticRelease.lean" ]]; then
  run_phase "semantic release (imports R-MC)" lake env lean \
    "$(realpath "$src/SemanticRelease.lean")" -o "$lib/SemanticRelease.olean"
fi
echo "$artifact render and semantic certificate modules kernel-checked"
