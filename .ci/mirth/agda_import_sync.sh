#!/usr/bin/env bash
set -euo pipefail

mode="${1:---check}"
case "$mode" in
  --check|--write) ;;
  *) echo "usage: agda-import-sync [--check|--write]" >&2; exit 2 ;;
esac

canonical="FullCoupled/CanonicalLearnerMonolith.agda"
lockdir=".ci/.mirth-agda-import-sync.lock"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"; rmdir "$lockdir" 2>/dev/null || true' EXIT INT TERM

[ -f "$canonical" ] || { echo "missing canonical learner: $canonical" >&2; exit 1; }

command_marker_file="$tmp/command.marker"
common_block_file="$tmp/common.block"
common_imports_file="$tmp/common.imports"

sed -n '/^-- BEGIN MIRTH-SYNC CANONICAL COMMAND$/,/^-- END MIRTH-SYNC CANONICAL COMMAND$/p' "$canonical" > "$command_marker_file"
sed -n '/^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/,/^-- END MIRTH-SYNC COMMON IMPORTS$/p' "$canonical" > "$common_block_file"

test "$(grep -Fc -- '-- BEGIN MIRTH-SYNC CANONICAL COMMAND' "$canonical")" -eq 1
test "$(grep -Fc -- '-- END MIRTH-SYNC CANONICAL COMMAND' "$canonical")" -eq 1
test "$(grep -Fc -- '-- BEGIN MIRTH-SYNC COMMON IMPORTS' "$canonical")" -eq 1
test "$(grep -Fc -- '-- END MIRTH-SYNC COMMON IMPORTS' "$canonical")" -eq 1
grep -Fqx -- '-- canonical-check-command = "$AGDA_COMMAND" -l standard-library -i .' <(grep -F -- 'canonical-check-command' "$command_marker_file")

sed '/^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/d;/^-- END MIRTH-SYNC COMMON IMPORTS$/d' "$common_block_file" |
  sed '/^-- Mirth-generated contract:/d;/^-- Solver-associated Base modules./d;/^-- Solver front ends./d;/^-- Existing shared semantics and container imports./d' > "$common_imports_file"

files="$(git ls-files '*.agda' | sort)"
test -n "$files"

check_command_surface() {
  local files
  files="$(printf '%s\n' flake.nix .ci/actions_ci.dhall .github/workflows/*.yml .github/workflows/*.yaml 2>/dev/null)"
  while IFS= read -r file; do
    [ -f "$file" ] || continue
    while IFS= read -r line; do
      [ -n "$line" ] || continue
      case "$line" in
        *'export AGDA_COMMAND='*) continue ;;
        *'"$AGDA_COMMAND" -l standard-library -i .'*) continue ;;
        *) echo "stale Agda command: $file:$line" >&2; return 1 ;;
      esac
    done < <(grep -F '"$AGDA_COMMAND"' "$file" || true)
  done <<< "$files"
}

check_file() {
  local file="$1"
  test "$(grep -Fc -- '-- BEGIN MIRTH-SYNC COMMON IMPORTS' "$file")" -eq 1
  test "$(grep -Fc -- '-- END MIRTH-SYNC COMMON IMPORTS' "$file")" -eq 1

  local actual_common
  actual_common="$(sed -n '/^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/,/^-- END MIRTH-SYNC COMMON IMPORTS$/p' "$file")"
  cmp -s "$common_block_file" <(printf '%s\n' "$actual_common")

  local duplicate
  duplicate="$(awk '
    BEGIN { inside=0 }
    /^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/ { inside=1; next }
    /^-- END MIRTH-SYNC COMMON IMPORTS$/ { inside=0; next }
    /^((open )?import)[[:space:]]+/ && !inside { print }
  ' "$file" | while IFS= read -r line; do
    grep -Fqx -- "$line" "$common_imports_file" && printf '%s\n' "$line"
  done)"
  test -z "$duplicate"
}

sync_file() {
  local file="$1"
  local candidate="$tmp/candidate"
  awk -v command_block="$command_marker_file" -v common_block="$common_block_file" -v canonical_imports="$common_imports_file" '
    function emit_file(path, line) {
      while ((getline line < path) > 0) print line
      close(path)
    }
    BEGIN {
      command=0
      common=0
      inserted=0
      while ((getline line < canonical_imports) > 0) {
        canonical[line]=1
      }
      close(canonical_imports)
    }
    /^-- BEGIN MIRTH-SYNC CANONICAL COMMAND$/ { command=1; next }
    command && /^-- END MIRTH-SYNC CANONICAL COMMAND$/ { command=0; next }
    /^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/ { common=1; next }
    common && /^-- END MIRTH-SYNC COMMON IMPORTS$/ { common=0; next }
    /^module[[:space:]]+[^[:space:]]+[[:space:]]+where[[:space:]]*$/ && inserted==0 {
      print
      emit_file(command_block)
      print ""
      emit_file(common_block)
      print ""
      inserted=1
      next
    }
    /^(open import|import)[[:space:]]+/ && canonical[$0] { next }
    { print }
    END { if (inserted==0) exit 3 }
  ' "$file" > "$candidate"
  mv "$candidate" "$file"
}

if [ "$mode" = "--write" ]; then
  attempt=0
  until mkdir "$lockdir" 2>/dev/null; do
    attempt=$((attempt + 1))
    if [ "$attempt" -ge 200 ]; then
      echo "mirth-agda-import-sync: lock timeout" >&2
      exit 1
    fi
    sleep 0.05
  done
  while IFS= read -r file; do
    [ -n "$file" ] || continue
    sync_file "$file"
  done <<< "$files"
fi

while IFS= read -r file; do
  [ -n "$file" ] || continue
  check_file "$file"
done <<< "$files"
check_command_surface

echo "mirth-agda-import-sync=pass"
echo "canonical-command=\"\$AGDA_COMMAND -l standard-library -i .\""
echo "shared-common-imports=byte-identical"
echo "source-set=git-ls-files-*.agda"
echo "write-path=lock-protected"
