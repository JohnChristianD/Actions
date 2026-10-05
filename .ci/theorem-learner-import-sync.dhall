let learnerModule : Text =
      "FullCoupled.CanonicalLearnerMonolith"
let learnerPath : Text =
      "FullCoupled/CanonicalLearnerMonolith.agda"
let theoremModule : Text =
      "FullCoupled.TheoremsMonolith"
let theoremPath : Text =
      "FullCoupled/TheoremsMonolith.agda"
let expectedImport : Text =
      "open import " ++ learnerModule ++ " as C"
in ''
#!/usr/bin/env bash
set -euo pipefail

learner="${learnerPath}"
theorem="${theoremPath}"
expected_import="${expectedImport}"
command_marker="-- canonical-check-command = \"$AGDA_COMMAND -i .\""

[ -f "$learner" ] || { echo "missing canonical learner: $learner"; exit 1; }
[ -f "$theorem" ] || { echo "missing theorem monolith: $theorem"; exit 1; }

grep -Fqx "module ${learnerModule} where" "$learner"
grep -Fqx "module ${theoremModule} where" "$theorem"
grep -Fxc "$expected_import" "$theorem" | grep -Fxq 1
grep -Fxc -- '-- BEGIN MIRTH-SYNC GLOBAL OPTIONS' "$learner" | grep -Fxq 1
grep -Fxc -- '-- BEGIN MIRTH-SYNC COMMON IMPORTS' "$learner" | grep -Fxq 1
grep -Fxc -- '-- BEGIN MIRTH-SYNC CANONICAL COMMAND' "$learner" | grep -Fxq 1
grep -Fqx "$command_marker" "$learner" || { echo "canonical Agda command drift"; exit 1; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
sed -n '/^-- BEGIN MIRTH-SYNC GLOBAL OPTIONS$/,/^-- END MIRTH-SYNC GLOBAL OPTIONS$/p' "$learner" > "$tmp/global"
sed -n '/^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/,/^-- END MIRTH-SYNC COMMON IMPORTS$/p' "$learner" > "$tmp/common"

failures=0
while IFS= read -r file; do
  test -n "$file" || continue
  actual="$tmp/actual"
  sed -n '/^-- BEGIN MIRTH-SYNC GLOBAL OPTIONS$/,/^-- END MIRTH-SYNC GLOBAL OPTIONS$/p' "$file" > "$actual"
  cmp -s "$actual" "$tmp/global" || {
    echo "global-option drift: $file"
    failures=$((failures + 1))
  }
  sed -n '/^-- BEGIN MIRTH-SYNC COMMON IMPORTS$/,/^-- END MIRTH-SYNC COMMON IMPORTS$/p' "$file" > "$actual"
  cmp -s "$actual" "$tmp/common" || {
    echo "common-import drift: $file"
    failures=$((failures + 1))
  }
done < <(git ls-files '*.agda' | sort)

test "$failures" -eq 0
echo "theorem-learner-import-sync=pass"
echo "canonical-command=$command_marker"
echo "all-agda-global-options=byte-identical"
echo "all-agda-common-imports=byte-identical"
''
