#!/usr/bin/env bash
set -euo pipefail

out="${1:?output DOT path}"
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

roots=(
  FullCoupled/CanonicalLearnerMonolith.agda
  FullCoupled/TheoremsMonolith.agda
)

: > "$tmp"
printf '%s\n' 'digraph AgdaShortMonolith {' > "$out"
printf '%s\n' '  rankdir=LR;' >> "$out"
printf '%s\n' '  "FullCoupled.CanonicalLearnerMonolith" [shape=box];' >> "$out"
printf '%s\n' '  "FullCoupled.TheoremsMonolith" [shape=box];' >> "$out"

for file in "${roots[@]}"; do
  module_name=$(awk '/^module[[:space:]]+/ {print $2; exit}' "$file")
  test -n "$module_name"

  while IFS= read -r imported; do
    [ -n "$imported" ] || continue
    printf '"%s" -> "%s" [label="imports"];\n' "$module_name" "$imported" >> "$tmp"
  done < <(
    sed -n 's/^[[:space:]]*open[[:space:]]\+import[[:space:]]\+\([^[:space:]]*\).*/\1/p;
           s/^[[:space:]]*import[[:space:]]\+\([^[:space:]]*\).*/\1/p' "$file"
  )
done

sort -u "$tmp" >> "$out"
printf '%s\n' '}' >> "$out"

printf 'agda-short-monolith-graph=pass\n'
printf 'roots=%s\n' "${#roots[@]}"
printf 'edges=%s\n' "$(grep -c -- ' -> ' "$out" || true)"
printf 'output=%s\n' "$out"
