#!/usr/bin/env bash
set -euo pipefail

agda_safe_files=(
  "Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
  "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"
)

run_agda_safe() {
  "$AGDA_COMMAND" --version
  "$AGDA_COMMAND" --safe -l standard-library -i . "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"

  for file in "${agda_safe_files[@]}"; do
    printf '==> Agda --safe %s\n' "$file"
    "$AGDA_COMMAND" --safe -l standard-library -i . "$file"
  done
}

run_mercury() {
  (
    cd ".ci"
    mmc --make check_forbidden_theorems
    ./check_forbidden_theorems
  )
}

run_discovery() {
  (
    cd ".ci/discovery"
    mmc --make theorem_monolith_egraph_sync
    ./theorem_monolith_egraph_sync
    mmc --make symbolic_egraph_test
    ./symbolic_egraph_test
    mmc --make interpolated_theorem_egraph_test
    ./interpolated_theorem_egraph_test
  )

  test -s ".ci/discovery/theorem-monolith-egraph-sync.json"
  printf '%s\n' "theorem-monolith-egraph-sync-report=present"
}

run_surface() {
  local theorem_monolith_count learner_monolith_count total_monolith_count

  theorem_monolith_count="$(
    find . -type f -not -path './.git/*' -print \
      | grep -F './Exotic/ERL/FullCoupled/TheoremsMonolith.agda' \
      | wc -l
  )"

  learner_monolith_count="$(
    find . -type f -not -path './.git/*' -print \
      | grep -F './Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda' \
      | wc -l
  )"

  total_monolith_count="$(
    find . -type f -not -path './.git/*' -name '*Monolith.agda' -print \
      | wc -l
  )"

  if [[ "$theorem_monolith_count" -ne 1 ]] ||
     [[ "$learner_monolith_count" -ne 1 ]] ||
     [[ "$total_monolith_count" -ne 2 ]] ||
     [[ -e "wiki" ]] ||
     [[ -e "Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda" ]]; then
    printf '%s\n' "ERROR: canonical surface requires exactly two monoliths: one learner and one theorem"
    find . -type f -not -path './.git/*' -name '*Monolith.agda' -print
    exit 1
  fi

  while IFS= read -r -d '' monolith; do
    case "${monolith#./}" in
      Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda|Exotic/ERL/FullCoupled/TheoremsMonolith.agda)
        ;;
      *)
        printf 'ERROR: noncanonical monolith remains: %s\n' "${monolith#./}"
        exit 1
        ;;
    esac
  done < <(find . -type f -not -path './.git/*' -name '*Monolith.agda' -print0)

  local bad_file
  while IFS= read -r -d '' bad_file; do
    local path="${bad_file#./}"
    case "$path" in
      .ci/ci.sh)
        continue
        ;;
      *.sh|*.bash|*.zsh|*.fish|*.cmd|*.bat|*.ps1|*.command|*.py|*.java|*.kt|*.scala|*.groovy|*.clj|*.cljs|*.js|*.mjs|*.cjs|*.ts|*.tsx|*.elm|*.purs|*.hs|*.lhs|*.cabal|*.c|*.h|*.cc|*.cpp|*.cxx|*.hpp|*.hxx|*.cs|*.fs|*.fsx|*.vb|*.csproj|*.fsproj|*.vbproj|*.sln|*.html|*.htm|*.css|*.tex|*.ltx|*.sty|*.cls|*.bib|*.scm|*.scheme|*.ss)
        printf 'ERROR: forbidden legacy/noncanonical source file: %s\n' "$path"
        exit 1
        ;;
      *)
        ;;
    esac
  done < <(find . -type f -not -path './.git/*' -print0)

  printf '%s\n' "single-theorem-source=TheoremsMonolith.agda; single-learner-source=CanonicalLearnerMonolith.agda; generated-Agda=absent; wiki=absent"
  local legacy_term_hits
  legacy_term_hits="$(
    grep -RniE --exclude-dir=.git --exclude=ci.sh \
      'guix|guile|(^|[^[:alnum:]])scheme([^[:alnum:]]|$)|evolutionary-search|evolutionary algorithm|Sparsemax2Pair|fixedTemperatureSparsemax|ActionScore|policyLeftWeight|TSTS|Gresher' . || true
  )"
  if [[ -n "$legacy_term_hits" ]]; then
    printf '%s\n' "ERROR: retired execution/search terminology remains in the repository:"
    printf '%s\n' "$legacy_term_hits"
    exit 1
  fi
  printf '%s\n' "surface=clean; retired execution/search terminology and noncanonical language files=absent"
}
run_versions() {
  nix --version
  "$AGDA_COMMAND" --version
  mmc --version
}

case "${1:-surface}" in
  agda-safe)
    run_agda_safe
    ;;
  mercury)
    run_mercury
    ;;
  discovery)
    run_discovery
    ;;
  surface)
    run_surface
    ;;
  versions)
    run_versions
    ;;
  all)
    run_versions
    run_agda_safe
    run_mercury
    run_discovery
    run_surface
    ;;
  *)
    printf 'usage: %s {agda-safe|mercury|discovery|surface|versions|all}\n' "$0"
    exit 2
    ;;
esac
