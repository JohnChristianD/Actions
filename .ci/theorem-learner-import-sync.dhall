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
learner_module="module ${learnerModule} where"
theorem_module="module ${theoremModule} where"
expected_import="${expectedImport}"

[ -f "$learner" ] || { echo "missing canonical learner: $learner"; exit 1; }
[ -f "$theorem" ] || { echo "missing theorem monolith: $theorem"; exit 1; }

grep -Fqx "$learner_module" "$learner" || {
  echo "learner module declaration does not match Dhall contract"
  exit 1
}
grep -Fqx "$theorem_module" "$theorem" || {
  echo "theorem module declaration does not match Dhall contract"
  exit 1
}

import_count=$(grep -Fxc "$expected_import" "$theorem")
[ "$import_count" -eq 1 ] || {
  echo "expected exactly one canonical learner import, found $import_count"
  exit 1
}

canonical_imports=$(grep -E "^(open )?import FullCoupled\\." "$theorem" || true)
unexpected_imports=$(printf '%s\\n' "$canonical_imports" | grep -Ev "^(open )?import FullCoupled\\.FormalMethods\\.|^open import FullCoupled\\.CanonicalLearnerMonolith as C$" || true)
[ -z "$unexpected_imports" ] || {
  echo "theorem monolith imports an unexpected FullCoupled semantic module:"
  printf '%s\\n' "$unexpected_imports"
  exit 1
}

echo "theorem-learner-import-sync=pass"
echo "learner_module=$learner_module"
echo "theorem_module=$theorem_module"
echo "theorem_import=$expected_import"
''
