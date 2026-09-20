#!/usr/bin/env bash
set -euo pipefail

agda_safe_files=(
  "Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
  "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"
  "Exotic/ERL/FullCoupled/NovelLearnerTheoremDiscovery_test.agda"
)

run_agda_safe() {
  agda --version
  agda --safe -l standard-library "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"

  for file in "${agda_safe_files[@]}"; do
    printf '==> Agda --safe %s\n' "$file"
    agda --safe -l standard-library "$file"
  done
}

run_mercury_egraph() {
  (
    cd ".ci"
    mmc --make check_forbidden_theorems
    ./check_forbidden_theorems
  )

  (
    cd ".ci/discovery"
    mmc --make theorem_monolith_egraph_sync
    ./theorem_monolith_egraph_sync
    mmc --make symbolic_egraph_test
    ./symbolic_egraph_test
    mmc --make interpolated_theorem_egraph_test
    ./interpolated_theorem_egraph_test
  )
}

run_mercury() {
  run_mercury_egraph
}

run_discovery() {
  run_mercury_egraph
  test -s ".ci/discovery/theorem-monolith-egraph-sync.json"
  printf '%s\n' "theorem-monolith-egraph-sync-report=present"
}

run_surface() {
  local monolith_count
  monolith_count="$(
    find . -type f -not -path './.git/*' -print       | grep -F '/Exotic/ERL/FullCoupled/TheoremsMonolith.agda'       | wc -l
  )"

  if [[ "$monolith_count" -ne 1 ]] ||
     [[ -e "wiki" ]] ||
     [[ -e "Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda" ]]; then
    printf '%s\n' "ERROR: theorem surface is not single-file canonical"
    exit 1
  fi

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

  printf '%s\n' "single-theorem-source=TheoremsMonolith.agda; generated-Agda=absent; wiki=absent"
  printf '%s\n' "surface=clean; legacy Scheme/Guix and noncanonical language files=absent"
}

run_versions() {
  nix --version
  agda --version
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
