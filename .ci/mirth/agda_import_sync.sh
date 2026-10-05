#!/usr/bin/env bash
set -euo pipefail

mode="${1:---check}"
canonical="FullCoupled/CanonicalLearnerMonolith.agda"
lockdir=".ci/.mirth-agda-import-sync.lock"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"; rmdir "$lockdir" 2>/dev/null || true' EXIT INT TERM

case "$mode" in
  --write|--check) ;;
  *) echo "usage: agda-import-sync [--write|--check]" >&2; exit 2 ;;
esac

[ -f "$canonical" ] || { echo "missing canonical learner: $canonical" >&2; exit 1; }

global="$tmp/global"
common="$tmp/common"
command="$tmp/command"

sed -n '/^-- BEGIN MIRTH-SYNC GLOBAL OPTIONS$/,/^-- END MIRTH-SYNC GLOBAL OPTIONS$/p' "$canonical" > "$global"
sed -n '/^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/,/^-- END MIRTH-SYNC COMMON IMPORTS$/p' "$canonical" > "$common"
sed -n '/^-- BEGIN MIRTH-SYNC CANONICAL COMMAND$/,/^-- END MIRTH-SYNC CANONICAL COMMAND$/p' "$canonical" > "$command"

test "$(grep -Fc -- '-- BEGIN MIRTH-SYNC GLOBAL OPTIONS' "$canonical")" -eq 1
test "$(grep -Fc -- '-- BEGIN MIRTH-SYNC COMMON IMPORTS' "$canonical")" -eq 1
test "$(grep -Fc -- '-- BEGIN MIRTH-SYNC CANONICAL COMMAND' "$canonical")" -eq 1
grep -Fqx -- '-- canonical-check-command = "$AGDA_COMMAND" -i .' <(grep -F -- 'canonical-check-command' "$command")

sources() {
  git ls-files '*.agda' | sort
}

rewrite_global() {
  local file="$1" out="$tmp/file"
  if grep -Fq -- '-- BEGIN MIRTH-SYNC GLOBAL OPTIONS' "$file"; then
    awk -v block="$global" '
      BEGIN { inside=0 }
      $0 == "-- BEGIN MIRTH-SYNC GLOBAL OPTIONS" {
        while ((getline line < block) > 0) print line
        close(block)
        inside=1
        next
      }
      $0 == "-- END MIRTH-SYNC GLOBAL OPTIONS" {
        inside=0
        next
      }
      !inside { print }
    ' "$file" > "$out"
  else
    {
      cat "$global"
      printf "\n"
      cat "$file"
    } > "$out"
  fi
  mv "$out" "$file"
}

rewrite_common() {
  local file="$1" out="$tmp/file"
  awk -v block="$common" '
    function emit(path, line) {
      while ((getline line < path) > 0) print line
      close(path)
    }
    BEGIN { inside=0; inserted=0 }
    $0 == "-- BEGIN MIRTH-SYNC COMMON IMPORTS" { inside=1; next }
    $0 == "-- END MIRTH-SYNC COMMON IMPORTS" {
      inside=0
      next
    }
    /^module[[:space:]]+[^[:space:]]+[[:space:]]+where[[:space:]]*$/ && inserted==0 {
      print
      printf "\n"
      emit(block)
      printf "\n"
      inserted=1
      next
    }
    !inside { print }
    END { if (inserted==0) exit 3 }
  ' "$file" > "$out"
  mv "$out" "$file"
}

check_global() {
  local file="$1" actual="$tmp/actual-global"
  sed -n '/^-- BEGIN MIRTH-SYNC GLOBAL OPTIONS$/,/^-- END MIRTH-SYNC GLOBAL OPTIONS$/p' "$file" > "$actual"
  cmp -s "$actual" "$global"
}

check_common() {
  local file="$1" actual="$tmp/actual-common"
  sed -n '/^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/,/^-- END MIRTH-SYNC COMMON IMPORTS$/p' "$file" > "$actual"
  cmp -s "$actual" "$common"
}

check_command_surfaces() {
  local file line bad=0
  for file in .ci/actions_ci.dhall .github/workflows/*.yml .github/workflows/*.yaml; do
    [ -f "$file" ] || continue
    while IFS= read -r line; do
      case "$line" in
        *'AGDA_COMMAND='*) continue ;;
        *'AGDA_COMMAND" --version'*) continue ;;
        *'AGDA_COMMAND" -i .'*) ;;
        *) echo "stale Agda command: $file:$line" >&2; bad=1 ;;
      esac
    done < <(grep -F '"$AGDA_COMMAND"' "$file" || true)
  done
  test "$bad" -eq 0
}

write_all() {
  local file
  mkdir "$lockdir"
  while IFS= read -r file; do
    [ -n "$file" ] || continue
    rewrite_global "$file"
    rewrite_common "$file"
  done < <(sources)
}

check_all() {
  local failures=0 file
  while IFS= read -r file; do
    [ -n "$file" ] || continue
    check_global "$file" || {
      echo "global-option drift: $file" >&2
      failures=$((failures + 1))
    }
    check_common "$file" || {
      echo "common-import drift: $file" >&2
      failures=$((failures + 1))
    }
  done < <(sources)
  check_command_surfaces || failures=$((failures + 1))
  test "$failures" -eq 0
}

case "$mode" in
  --write)
    write_all
    ;;
  --check)
    ;;
esac

check_all

echo "mirth-agda-import-sync=pass"
echo "canonical=$canonical"
echo "synced-agda-files=$(sources | wc -l | tr -d ' ')"
echo 'canonical-command="$AGDA_COMMAND -i ."'
echo "global-options=canonical"
echo "common-imports=canonical"
echo "command-surfaces=canonical"
