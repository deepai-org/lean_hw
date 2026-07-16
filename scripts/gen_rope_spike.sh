#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 LINES_PER_LEAF OUTPUT.lean" >&2
  exit 2
fi

leaf_size=$1
out=$2
total_lines=187948

mkdir -p "$(dirname "$out")"
: > "$out"

printf '%s\n' \
  '-- Generated full-scale release-proof feasibility spike.' \
  'set_option maxRecDepth 1000000' \
  'set_option maxHeartbeats 0' \
  '' \
  'namespace Loom.Generated.RopeSpike' \
  '' \
  'inductive Rope (α : Type) where' \
  '  | leaf (value : α)' \
  '  | node (left right : Rope α)' \
  '' \
  'structure Item where' \
  '  lines : List String' \
  '' \
  'def renderItem (item : Item) : List String := item.lines' \
  '' \
  'def renderTree : Rope Item → Rope (List String)' \
  '  | .leaf item => .leaf (renderItem item)' \
  '  | .node left right => .node (renderTree left) (renderTree right)' \
  '' \
  'def flatten : Rope (List String) → String' \
  '  | .leaf lines => String.intercalate "\n" lines' \
  '  | .node left right => flatten left ++ "\n" ++ flatten right' \
  '' \
  'structure Pair where' \
  '  witness : Rope Item' \
  '  disk : Rope (List String)' \
  '' >> "$out"

leaf_count=$(( (total_lines + leaf_size - 1) / leaf_size ))
for ((leaf=0; leaf<leaf_count; leaf++)); do
  first=$(( leaf * leaf_size ))
  last=$(( first + leaf_size ))
  if (( last > total_lines )); then last=$total_lines; fi
  printf 'def pair_%d : Pair where\n  witness := .leaf { lines := [\n' "$leaf" >> "$out"
  for ((line=first; line<last; line++)); do
    sep=','
    if (( line + 1 == last )); then sep=''; fi
    printf '    "  wire [31:0] dummy_%d = 32\x27d%d;"%s\n' "$line" "$line" "$sep" >> "$out"
  done
  printf '  ] }\n  disk := .leaf [\n' >> "$out"
  for ((line=first; line<last; line++)); do
    sep=','
    if (( line + 1 == last )); then sep=''; fi
    printf '    "  wire [31:0] dummy_%d = 32\x27d%d;"%s\n' "$line" "$line" "$sep" >> "$out"
  done
  printf ']\n\ntheorem proof_%d : renderTree pair_%d.witness = pair_%d.disk := by rfl\n\n' \
    "$leaf" "$leaf" "$leaf" >> "$out"
done

level=0
ids=()
for ((i=0; i<leaf_count; i++)); do ids+=("$i"); done
next_id=$leaf_count

while (( ${#ids[@]} > 1 )); do
  next=()
  for ((i=0; i<${#ids[@]}; i+=2)); do
    left=${ids[i]}
    if (( i + 1 == ${#ids[@]} )); then
      next+=("$left")
      continue
    fi
    right=${ids[i+1]}
    id=$next_id
    next_id=$((next_id + 1))
    printf 'def pair_%d : Pair where\n  witness := .node pair_%s.witness pair_%s.witness\n  disk := .node pair_%s.disk pair_%s.disk\n\n' \
      "$id" "$left" "$right" "$left" "$right" >> "$out"
    printf 'theorem proof_%d : renderTree pair_%d.witness = pair_%d.disk := by\n  rw [pair_%d]\n  simp only [renderTree]\n  rw [proof_%s, proof_%s]\n\n' \
      "$id" "$id" "$id" "$id" "$left" "$right" >> "$out"
    next+=("$id")
  done
  ids=("${next[@]}")
  level=$((level + 1))
done

root=${ids[0]}
printf '%s\n' \
  'def SemanticallyRefines (_ : Rope (List String)) : Prop := True' \
  '' \
  '/-- The intended release-theorem shape: exact flattened bytes plus a' \
  'placeholder for the composed semantic refinement result. -/' \
  "theorem releaseShape : flatten pair_${root}.disk =" \
  "    flatten (renderTree pair_${root}.witness) ∧" \
  "    SemanticallyRefines pair_${root}.disk := by" \
  "  exact ⟨congrArg flatten proof_${root}.symm, trivial⟩" \
  '' \
  "#print axioms releaseShape" \
  '' \
  'end Loom.Generated.RopeSpike' >> "$out"

echo "generated $leaf_count leaves, $next_id pairs, depth $level in $out"
