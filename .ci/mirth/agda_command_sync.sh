#!/usr/bin/env bash
set -euo pipefail
canonical=FullCoupled/CanonicalLearnerMonolith.agda
theorem_graph=FullCoupled/TheoremsMonolith.agda
mode="${1:---check}"
block=$(mktemp)
tmp=$(mktemp)
theorem_graph_block=$(mktemp)
theorem_graph_plain_block=$(mktemp)
trap 'rm -f "$block" "$tmp" "$theorem_graph_block" "$theorem_graph_plain_block"' EXIT
sources() { git ls-files '*.agda' | LC_ALL=C sort; }
extract_block() { sed -n '/^-- BEGIN MIRTH-SYNC CANONICAL COMMAND$/,/^-- END MIRTH-SYNC CANONICAL COMMAND$/p' "$1"; }
extract_block "$canonical" > "$block"
[ -s "$block" ] || { echo 'canonical command block missing' >&2; exit 1; }
check_one() { file="$1"; extract_block "$file" | cmp -s "$block"; }
write_graph_block() {
  local start="$1"
  local end="$2"
  local block_file="$3"
  if grep -Fq -- "$start" "$theorem_graph"; then
    awk -v block="$block_file" -v start="$start" -v end="$end" '
      $0 == start {
        while ((getline line < block) > 0) print line
        close(block); inside=1; next
      }
      $0 == end { inside=0; next }
      !inside { print }
    ' "$theorem_graph" > "$tmp"
  else
    awk -v block="$block_file" -v marker="$4" '
      $0 == marker {
        print
        while ((getline line < block) > 0) print line
        close(block)
        next
      }
      { print }
    ' "$theorem_graph" > "$tmp"
  fi
  mv "$tmp" "$theorem_graph"
}
check_theorem_graph_command() {
  {
    printf '%s\n' '-- BEGIN MIRTH-SYNC THEOREM GRAPH COMMAND'
    printf '%s\n' '-- "$AGDA_COMMAND" --dependency-graph=.ci/discovery/theorems-monolith.dot -i . FullCoupled/TheoremsMonolith.agda'
    printf '%s\n' '-- END MIRTH-SYNC THEOREM GRAPH COMMAND'
  } > "$theorem_graph_block"
  {
    printf '%s\n' '-- BEGIN THEOREM GRAPH COMMAND'
    printf '%s\n' '-- "$AGDA_COMMAND" --dependency-graph=.ci/discovery/theorems-monolith.dot -i . FullCoupled/TheoremsMonolith.agda'
    printf '%s\n' '-- END THEOREM GRAPH COMMAND'
  } > "$tmp"
  sed -n '/^-- BEGIN MIRTH-SYNC THEOREM GRAPH COMMAND$/,/^-- END MIRTH-SYNC THEOREM GRAPH COMMAND$/p' "$theorem_graph" | cmp -s "$theorem_graph_block"
  sed -n '/^-- BEGIN THEOREM GRAPH COMMAND$/,/^-- END THEOREM GRAPH COMMAND$/p' "$theorem_graph" | cmp -s "$tmp"
}
rewrite_theorem_graph_command() {
  {
    printf '%s\n' '-- BEGIN MIRTH-SYNC THEOREM GRAPH COMMAND'
    printf '%s\n' '-- "$AGDA_COMMAND" --dependency-graph=.ci/discovery/theorems-monolith.dot -i . FullCoupled/TheoremsMonolith.agda'
    printf '%s\n' '-- END MIRTH-SYNC THEOREM GRAPH COMMAND'
  } > "$theorem_graph_block"
  {
    printf '%s\n' '-- BEGIN THEOREM GRAPH COMMAND'
    printf '%s\n' '-- "$AGDA_COMMAND" --dependency-graph=.ci/discovery/theorems-monolith.dot -i . FullCoupled/TheoremsMonolith.agda'
    printf '%s\n' '-- END THEOREM GRAPH COMMAND'
  } > "$tmp"
  write_graph_block     '-- BEGIN MIRTH-SYNC THEOREM GRAPH COMMAND'     '-- END MIRTH-SYNC THEOREM GRAPH COMMAND'     "$theorem_graph_block"     '-- END MIRTH-SYNC CANONICAL COMMAND'
  write_graph_block     '-- BEGIN THEOREM GRAPH COMMAND'     '-- END THEOREM GRAPH COMMAND'     "$tmp"     '-- END MIRTH-SYNC THEOREM GRAPH COMMAND'
}
rewrite_one() {
  file="$1"
  if grep -Fq -- '-- BEGIN MIRTH-SYNC CANONICAL COMMAND' "$file"; then
    awk -v block="$block" '
      $0 == "-- BEGIN MIRTH-SYNC CANONICAL COMMAND" {
        while ((getline line < block) > 0) print line
        close(block); inside=1; next
      }
      $0 == "-- END MIRTH-SYNC CANONICAL COMMAND" { inside=0; next }
      !inside { print }
    ' "$file" > "$tmp"
  else
    awk -v block="$block" '
      /^module[[:space:]].*where[[:space:]]*$/ {
        print; print ""
        while ((getline line < block) > 0) print line
        close(block); print ""; next
      }
      { print }
    ' "$file" > "$tmp"
  fi
  mv "$tmp" "$file"
}
if [ "$mode" = "--check" ]; then
  failures=0
  while IFS= read -r file; do
    check_one "$file" || { echo "canonical command drift: $file" >&2; failures=$((failures + 1)); }
  done < <(sources)
  test "$failures" -eq 0
elif [ "$mode" = "--write" ]; then
  while IFS= read -r file; do rewrite_one "$file"; done < <(sources)
  rewrite_theorem_graph_command
else
  echo 'usage: agda-command-sync [--check|--write]' >&2
  exit 2
fi
echo 'mirth-agda-command-sync=pass'
check_theorem_graph_command
echo "theorem-graph-command=$theorem_graph"
