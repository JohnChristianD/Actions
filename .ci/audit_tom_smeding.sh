#!/usr/bin/env bash
set -euo pipefail

repo=.ci/external/efficient-chad-agda
pruned=.ci/external/efficient-chad-pruned
roots=(chad-cost.agda chad-preserves-primal.agda)

rm -rf "$pruned"
mkdir -p "$pruned"

declare -A seen
queue=()
for root in "${roots[@]}"; do
  queue+=("$root")
done

while ((${#queue[@]} > 0)); do
  current=${queue[0]}
  queue=("${queue[@]:1}")
  [[ -n "${seen[$current]:-}" ]] && continue
  seen[$current]=1

  src="$repo/$current"
  [[ -f "$src" ]] || continue
  mkdir -p "$pruned/$(dirname "$current")"
  cp "$src" "$pruned/$current"

  while read -r imported; do
    [[ -n "$imported" ]] || continue
    candidate="${imported//./\/}.agda"
    if [[ -f "$repo/$candidate" && -z "${seen[$candidate]:-}" ]]; then
      queue+=("$candidate")
    fi
  done < <(grep -hoE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+[A-Za-z0-9_.-]+' "$src" | sed -E 's/^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+//')
done

find "$pruned" -type f -name '*.agda' | sort > "$pruned/MANIFEST"

grep -RhoE '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+[A-Za-z0-9_.-]+' "$pruned" --include='*.agda' \
  | sed -E 's/^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+//' \
  | sort -u > "$pruned/IMPORTS"

if grep -Eq '^(Data|Function|Relation)(\.|$)' "$pruned/IMPORTS"; then
  echo 'pruned-closure-stdlib-dependencies=DETECTED'
else
  echo 'pruned-closure-stdlib-dependencies=NONE'
fi

echo 'pruned-local-file-count='"$(grep -c '\.agda$' "$pruned/MANIFEST")"
echo 'pruned-closure-manifest:'
cat "$pruned/MANIFEST"
echo 'pruned-import-manifest:'
cat "$pruned/IMPORTS"
