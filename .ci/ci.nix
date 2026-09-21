{ writeShellApplication
, mercury
, gnumake
, git
, coreutils
, findutils
, gnugrep
}:

writeShellApplication {
  name = "actions-ci";
  runtimeInputs = [
    mercury
    gnumake
    git
    coreutils
    findutils
    gnugrep
  ];
  text = ''
    set -euo pipefail

    run_agda_file() {
      local file="$1"
      printf '==> Agda --safe %s\n' "$file"
      timeout --foreground "''${AGDA_TIMEOUT_SECONDS:-1200}" "$AGDA_COMMAND" --safe -l standard-library -i . "$file"
    }

    run_agda_learner() {
      "$AGDA_COMMAND" --version
      run_agda_file "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith_test.agda"
    }

    run_agda_theorem() {
      "$AGDA_COMMAND" --version
      run_agda_file "Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
    }

    run_agda_safe() {
      run_agda_learner
      run_agda_theorem
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
      grep -q '"forced_symbolic_target": false' ".ci/discovery/theorem-monolith-egraph-sync.json"
      grep -q '"single_agda_source": true' ".ci/discovery/theorem-monolith-egraph-sync.json"
      grep -q '"astar_search": "structural dependency composition only"' ".ci/discovery/theorem-monolith-egraph-sync.json"
      astar_count="$(sed -n 's/.*"astar_emergent_candidate_count": \\([0-9][0-9]*\\).*/\\1/p' ".ci/discovery/theorem-monolith-egraph-sync.json")"
      test -n "$astar_count"
      test "$astar_count" -gt 0
      printf 'theorem-monolith-egraph-sync-report=present\n'
      printf 'astar-emergent-candidate-count=%s\n' "$astar_count"
    }

    run_semantic_contract() {
      local theorem="Exotic/ERL/FullCoupled/TheoremsMonolith.agda"
      local required=(
        "CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem"
        "canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class"
        "FiniteHardSparseKKTEquilibriumTheorem"
        "DirectProductFiniteAutomatonComposition"
        "canonical-recurrent-prefix-monoid-homomorphism"
        "canonical-hadamard-attention-rope-prefix-composition-theorem"
        "ContinuousLeftInverseTheorem"
        "canonicalRingStateInjective"
        "canonicalDenseNeighborhoodSeparation"
        "canonicalPigeonholeNatClockContradiction"
        "canonicalNoGlobalInt8DiscreteUAPOnOrbit"
        "canonicalNoNontrivialFiniteCycle-theorem"
        "canonicalDeterministicFiniteStepDivergenceInevitability"
        "canonicalNoFiniteStepConvergenceToFixedPoint"
        "BairdSevenStarProblem"
        "bairdSevenStar"
        "NonIIDMarkovWalrasianProblem"
        "nonIIDMarkovStationaryWalrasian-lift"
        "Majority3ShapleyEquilibrium"
        "majority3ShapleyEquilibriumWitness"
      )
      for symbol in "''${required[@]}"; do
        if ! grep -Fq "$symbol" "$theorem"; then
          printf 'ERROR: canonical theorem semantic missing: %s\n' "$symbol"
          exit 1
        fi
      done
      if grep -Eiq 'target[-_ ]network|(^|[^[:alnum:]])normalization([^[:alnum:]]|$)|(^|[^[:alnum:]])regularization([^[:alnum:]]|$)' "Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda"; then
        printf '%s\n' 'ERROR: forbidden extraneous target-network/normalization/regularization semantics entered the canonical learner'
        exit 1
      fi
      if ! grep -Fq 'open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C' "$theorem"; then
        printf '%s\n' 'ERROR: theorem monolith is not sourced from the canonical learner monolith'
        exit 1
      fi
      printf '%s\n' 'semantic-contract=clean; canonical learner/theorem load-bearing semantics present; forbidden extras absent'
    }

    run_surface() {
      local theorem_monolith_count learner_monolith_count total_monolith_count
      if grep -Eq '^[[:space:]]+cancel-in-progress:[[:space:]]+true' .github/workflows/nix-composition.yml; then
        printf '%s\n' 'ERROR: CI concurrency is allowed only when runs cannot be cancelled'
        exit 1
      fi
      theorem_monolith_count="$(find . -type f -not -path './.git/*' -print | grep -Fc './Exotic/ERL/FullCoupled/TheoremsMonolith.agda')"
      learner_monolith_count="$(find . -type f -not -path './.git/*' -print | grep -Fc './Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda')"
      total_monolith_count="$(find . -type f -not -path './.git/*' -name '*Monolith.agda' -print | wc -l)"
      if [[ "$theorem_monolith_count" -ne 1 ]] || [[ "$learner_monolith_count" -ne 1 ]] || [[ "$total_monolith_count" -ne 2 ]] || [[ -e "wiki" ]] || [[ -e "Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda" ]]; then
        printf '%s\n' 'ERROR: canonical surface requires exactly two monoliths: one learner and one theorem'
        find . -type f -not -path './.git/*' -name '*Monolith.agda' -print
        exit 1
      fi
      while IFS= read -r monolith; do
        case "$monolith" in
          Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda|Exotic/ERL/FullCoupled/TheoremsMonolith.agda) ;;
          *) printf 'ERROR: noncanonical monolith remains: %s\n' "$monolith"; exit 1 ;;
        esac
      done < <(find . -type f -not -path './.git/*' -name '*Monolith.agda' -print)
      local bad_file
      while IFS= read -r bad_file; do
        local path="$bad_file"
        case "$path" in
          ./.ci/ci.sh) printf '%s\n' 'ERROR: hand-maintained shell workflow remains; use .ci/ci.nix'; exit 1 ;;
          ./*.sh|./*.bash|./*.zsh|./*.fish|./*.cmd|./*.bat|./*.ps1|./*.command|./*.py|*.java|*.kt|*.scala|*.groovy|*.clj|*.cljs|*.js|*.mjs|*.cjs|*.ts|*.tsx|*.elm|*.purs|*.hs|*.lhs|*.cabal|*.c|*.h|*.cc|*.cpp|*.cxx|*.hpp|*.hxx|*.cs|*.fs|*.fsx|*.vb|*.csproj|*.fsproj|*.vbproj|*.sln|*.html|*.htm|*.css|*.tex|*.ltx|*.sty|*.cls|*.bib|*.scm|*.scheme|*.ss)
            printf 'ERROR: forbidden legacy/noncanonical source file: %s\n' "$path"; exit 1 ;;
          *) ;;
        esac
      done < <(find . -type f -not -path './.git/*' -print)
      printf '%s\n' 'single-theorem-source=TheoremsMonolith.agda; single-learner-source=CanonicalLearnerMonolith.agda; generated-Agda=absent; wiki=absent'
      local legacy_term_hits
      legacy_term_hits="$(grep -RniE --exclude-dir=.git --exclude=ci.nix 'guix|guile|(^|[^[:alnum:]])scheme([^[:alnum:]]|$)|evolutionary-search|evolutionary algorithm|Sparsemax2Pair|fixedTemperatureSparsemax|ActionScore|policyLeftWeight|TSTS|Gresher' . || true)"
      if [[ -n "$legacy_term_hits" ]]; then
        printf '%s\n' 'ERROR: retired execution/search terminology remains in the repository:'
        printf '%s\n' "$legacy_term_hits"
        exit 1
      fi
      printf '%s\n' 'surface=clean; retired execution/search terminology and noncanonical language files=absent'
    }

    run_versions() {
      nix --version
      "$AGDA_COMMAND" --version
      mmc --version
    }

    case "''${1:-surface}" in
      agda-learner) run_agda_learner ;;
      agda-theorem) run_agda_theorem ;;
      agda-safe) run_agda_safe ;;
      mercury) run_mercury ;;
      discovery) run_discovery ;;
      semantic-contract) run_semantic_contract ;;
      surface) run_surface ;;
      versions) run_versions ;;
      all)
        run_versions
        run_agda_safe
        run_mercury
        run_discovery
        run_semantic_contract
        run_surface
        ;;
      *)
        printf 'usage: %s {agda-safe|agda-learner|agda-theorem|mercury|discovery|semantic-contract|surface|versions|all}\n' "$0"
        exit 2
        ;;
    esac
  '';
}
\0' monolith; do
        case "$monolith" in
          Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda|Exotic/ERL/FullCoupled/TheoremsMonolith.agda) ;;
          *) printf 'ERROR: noncanonical monolith remains: %s\n' "$monolith"; exit 1 ;;
        esac
      done < <(find . -type f -not -path './.git/*' -name '*Monolith.agda' -print0)
      local bad_file
      while IFS= read -r -d  bad_file; do
        local path="$bad_file"
        case "$path" in
          ./.ci/ci.sh) printf '%s\n' 'ERROR: hand-maintained shell workflow remains; use .ci/ci.nix'; exit 1 ;;
          ./*.sh|./*.bash|./*.zsh|./*.fish|./*.cmd|./*.bat|./*.ps1|./*.command|./*.py|*.java|*.kt|*.scala|*.groovy|*.clj|*.cljs|*.js|*.mjs|*.cjs|*.ts|*.tsx|*.elm|*.purs|*.hs|*.lhs|*.cabal|*.c|*.h|*.cc|*.cpp|*.cxx|*.hpp|*.hxx|*.cs|*.fs|*.fsx|*.vb|*.csproj|*.fsproj|*.vbproj|*.sln|*.html|*.htm|*.css|*.tex|*.ltx|*.sty|*.cls|*.bib|*.scm|*.scheme|*.ss)
            printf 'ERROR: forbidden legacy/noncanonical source file: %s\n' "$path"; exit 1 ;;
          *) ;;
        esac
      done < <(find . -type f -not -path './.git/*' -print0)
      printf '%s\n' 'single-theorem-source=TheoremsMonolith.agda; single-learner-source=CanonicalLearnerMonolith.agda; generated-Agda=absent; wiki=absent'
      local legacy_term_hits
      legacy_term_hits="$(grep -RniE --exclude-dir=.git --exclude=ci.nix 'guix|guile|(^|[^[:alnum:]])scheme([^[:alnum:]]|$)|evolutionary-search|evolutionary algorithm|Sparsemax2Pair|fixedTemperatureSparsemax|ActionScore|policyLeftWeight|TSTS|Gresher' . || true)"
      if [[ -n "$legacy_term_hits" ]]; then
        printf '%s\n' 'ERROR: retired execution/search terminology remains in the repository:'
        printf '%s\n' "$legacy_term_hits"
        exit 1
      fi
      printf '%s\n' 'surface=clean; retired execution/search terminology and noncanonical language files=absent'
    }

    run_versions() {
      nix --version
      "$AGDA_COMMAND" --version
      mmc --version
    }

    case "''${1:-surface}" in
      agda-learner) run_agda_learner ;;
      agda-theorem) run_agda_theorem ;;
      agda-safe) run_agda_safe ;;
      mercury) run_mercury ;;
      discovery) run_discovery ;;
      semantic-contract) run_semantic_contract ;;
      surface) run_surface ;;
      versions) run_versions ;;
      all)
        run_versions
        run_agda_safe
        run_mercury
        run_discovery
        run_semantic_contract
        run_surface
        ;;
      *)
        printf 'usage: %s {agda-safe|agda-learner|agda-theorem|mercury|discovery|semantic-contract|surface|versions|all}\n' "$0"
        exit 2
        ;;
    esac
  '';
}
\0' bad_file; do
        local path="$bad_file"
        case "$path" in
          ./.ci/ci.sh) printf '%s\n' 'ERROR: hand-maintained shell workflow remains; use .ci/ci.nix'; exit 1 ;;
          ./*.sh|./*.bash|./*.zsh|./*.fish|./*.cmd|./*.bat|./*.ps1|./*.command|./*.py|*.java|*.kt|*.scala|*.groovy|*.clj|*.cljs|*.js|*.mjs|*.cjs|*.ts|*.tsx|*.elm|*.purs|*.hs|*.lhs|*.cabal|*.c|*.h|*.cc|*.cpp|*.cxx|*.hpp|*.hxx|*.cs|*.fs|*.fsx|*.vb|*.csproj|*.fsproj|*.vbproj|*.sln|*.html|*.htm|*.css|*.tex|*.ltx|*.sty|*.cls|*.bib|*.scm|*.scheme|*.ss)
            printf 'ERROR: forbidden legacy/noncanonical source file: %s\n' "$path"; exit 1 ;;
          *) ;;
        esac
      done < <(find . -type f -not -path './.git/*' -print0)
      printf '%s\n' 'single-theorem-source=TheoremsMonolith.agda; single-learner-source=CanonicalLearnerMonolith.agda; generated-Agda=absent; wiki=absent'
      local legacy_term_hits
      legacy_term_hits="$(grep -RniE --exclude-dir=.git --exclude=ci.nix 'guix|guile|(^|[^[:alnum:]])scheme([^[:alnum:]]|$)|evolutionary-search|evolutionary algorithm|Sparsemax2Pair|fixedTemperatureSparsemax|ActionScore|policyLeftWeight|TSTS|Gresher' . || true)"
      if [[ -n "$legacy_term_hits" ]]; then
        printf '%s\n' 'ERROR: retired execution/search terminology remains in the repository:'
        printf '%s\n' "$legacy_term_hits"
        exit 1
      fi
      printf '%s\n' 'surface=clean; retired execution/search terminology and noncanonical language files=absent'
    }

    run_versions() {
      nix --version
      "$AGDA_COMMAND" --version
      mmc --version
    }

    case "''${1:-surface}" in
      agda-learner) run_agda_learner ;;
      agda-theorem) run_agda_theorem ;;
      agda-safe) run_agda_safe ;;
      mercury) run_mercury ;;
      discovery) run_discovery ;;
      semantic-contract) run_semantic_contract ;;
      surface) run_surface ;;
      versions) run_versions ;;
      all)
        run_versions
        run_agda_safe
        run_mercury
        run_discovery
        run_semantic_contract
        run_surface
        ;;
      *)
        printf 'usage: %s {agda-safe|agda-learner|agda-theorem|mercury|discovery|semantic-contract|surface|versions|all}\n' "$0"
        exit 2
        ;;
    esac
  '';
}
