#!/usr/bin/env bash
set -euo pipefail

out="${1:?output Elm module path}"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

sources=$(git ls-files '*.agda')
test -n "$sources"

: > "$tmp/nodes.tsv"
: > "$tmp/edges.tsv"

while IFS= read -r file; do
  module_name=$(awk '/^module[[:space:]]+/ {print $2; exit}' "$file")
  test -n "$module_name"
  printf '%s\t%s\t%s\n' "$module_name" "$module_name" "$file" >> "$tmp/nodes.tsv"

  while IFS= read -r imported; do
    [ -n "$imported" ] || continue
    printf '%s\t%s\timports\n' "$module_name" "$imported" >> "$tmp/edges.tsv"
  done < <(sed -n 's/^[[:space:]]*open[[:space:]]\+import[[:space:]]\+\([^[:space:]]*\).*/\1/p; s/^[[:space:]]*import[[:space:]]\+\([^[:space:]]*\).*/\1/p' "$file")
done <<< "$sources"

{
  printf '%s\n' 'module GeneratedAgdaGraph exposing (Node, Edge, nodes, edges)'
  printf '%s\n' 'type alias Node = { id : String, label : String, source : String }'
  printf '%s\n' 'type alias Edge = { source : String, target : String, relation : String }'
  printf '%s\n' 'nodes : List Node'
  printf '%s\n' 'nodes ='
  if [ -s "$tmp/nodes.tsv" ]; then
    awk -F '\t' 'BEGIN { OFS="" } {
      printf "    { id = \"%s\", label = \"%s\", source = \"%s\" } ::\n", $1, $2, $3
    }' "$tmp/nodes.tsv"
  fi
  printf '%s\n' '    []'
  printf '%s\n' 'edges : List Edge'
  printf '%s\n' 'edges ='
  if [ -s "$tmp/edges.tsv" ]; then
    awk -F '\t' 'BEGIN { OFS="" } {
      printf "    { source = \"%s\", target = \"%s\", relation = \"%s\" } ::\n", $1, $2, $3
    }' "$tmp/edges.tsv"
  fi
  printf '%s\n' '    []'
} > "$out"

printf '%s\n' 'Generated Agda import graph:' "$out"
wc -l "$out"
