let lane = env:CI_LANE as Text

let script =
  if lane == "agda-learner" then
    ''
    set -euo pipefail
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    ''
  else if lane == "agda-theorem" then
    ''
    set -euo pipefail
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    ''
  else if lane == "agda-safe" then
    ''
    set -euo pipefail
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    ''
  else if lane == "mercury" then
    ''
    set -euo pipefail
    mmc --make .ci/check_forbidden_theorems
    ./.ci/check_forbidden_theorems
    ''
  else if lane == "discovery" then
    ''
    set -euo pipefail
    mmc --make .ci/discovery/theorem_monolith_egraph_sync
    ./.ci/discovery/theorem_monolith_egraph_sync
    mmc --make .ci/discovery/symbolic_egraph_test
    ./.ci/discovery/symbolic_egraph_test
    mmc --make .ci/discovery/interpolated_theorem_egraph_test
    ./.ci/discovery/interpolated_theorem_egraph_test
    report=.ci/discovery/theorem-monolith-egraph-sync.json
    grep -Fq '"forced_symbolic_target": true' "$report" && { echo "forced symbolic target"; exit 1; } || true
    grep -Fq '"single_agda_source": false' "$report" && { echo "non-canonical Agda source"; exit 1; } || true
    grep -Fq '"graph_search": "A* cost-guided dependency paths"' "$report" || { echo "missing A* graph label"; exit 1; }
    grep -Fq '"astar_score_ordered": true' "$report" || { echo "A* order gate failed"; exit 1; }
    grep -Fq '"emergent_composition_count": 0' "$report" && { echo "no emergent composition"; exit 1; } || true
    ''
  else if lane == "econlib-crossrepo" then
    ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git clone --quiet --depth 1 https://github.com/danlyng/Econlib.git "$tmp/Econlib"
    econlib_rev=$(git -C "$tmp/Econlib" rev-parse HEAD)

    upstream_economy="$tmp/Econlib/Econlib/Equilibrium/Economy.lean"
    upstream_existence="$tmp/Econlib/Econlib/Equilibrium/Existence.lean"
    upstream_markov="$tmp/Econlib/EconlibExamples/Equilibrium/MarkovStationary.lean"
    local_theorem="Exotic/ERL/FullCoupled/TheoremsMonolith.agda"

    grep -Fq 'structure WalrasianEquilibrium' "$upstream_economy"
    grep -Fq 'theorem exists_equilibrium' "$upstream_existence"
    grep -Fq 'Nonempty E.WalrasianEquilibrium' "$upstream_existence"
    grep -Fq 'stationary Walrasian equilibrium' "$upstream_markov"

    grep -Fq 'staticWalrasian' "$local_theorem"
    grep -Fq 'GeneralizedWalrasianEquilibrium' "$local_theorem"
    grep -Fq 'generalizedWalrasianEquilibrium-from-static' "$local_theorem"
    grep -Fq 'MarkovStationaryWalrasianCompositionTheorem' "$local_theorem"
    grep -Fq 'markov-stationary-walrasian-composition-theorem' "$local_theorem"

    adapter_present=false
    if grep -Eiq 'Econlib|exists_equilibrium' "$local_theorem"; then
      adapter_present=true
    fi

    mkdir -p .ci/discovery
    {
      printf '%s\n' '{'
      printf '  "econlib_repo": "danlyng/Econlib",\n'
      printf '  "econlib_commit": "%s",\n' "$econlib_rev"
      printf '  "upstream_static_existence": "Economy.exists_equilibrium",\n'
      printf '  "upstream_equilibrium_object": "Economy.WalrasianEquilibrium",\n'
      printf '  "local_static_target": "staticWalrasian",\n'
      printf '  "local_stationary_lift": "generalizedWalrasianEquilibrium-from-static",\n'
      printf '  "local_markov_composition": "markov-stationary-walrasian-composition-theorem",\n'
      printf '  "adapter_present": %s,\n' "$adapter_present"
      printf '  "composition_path": ["Econlib::Economy.exists_equilibrium", "bridge::staticWalrasian", "Actions::generalizedWalrasianEquilibrium-from-static", "Actions::markov-stationary-walrasian-composition-theorem"],\n'
      printf '  "graph_status": "composition-ready; explicit cross-language adapter still required"\n'
      printf '%s\n' '}'
    } > .ci/discovery/econlib-crossrepo-sync.json

    grep -Fq '"upstream_static_existence": "Economy.exists_equilibrium"' .ci/discovery/econlib-crossrepo-sync.json
    grep -Fq '"local_stationary_lift": "generalizedWalrasianEquilibrium-from-static"' .ci/discovery/econlib-crossrepo-sync.json
    echo "econlib-crossrepo-sync=pass"
    echo "econlib-commit=$econlib_rev"
    echo "adapter-present=$adapter_present"
    ''
  else if lane == "semantic-contract" then
    ''
    set -euo pipefail
    theorem=Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    learner=Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    required='
    CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
    canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class
    FiniteHardSparseKKTEquilibriumTheorem
    DirectProductFiniteAutomatonComposition
    canonical-recurrent-prefix-monoid-homomorphism
    canonicalF4-prefix-monoid-homomorphism
    canonicalNormPair-prefix-monoid-homomorphism
    canonicalGRUF4Norm-prefix-monoid-homomorphism
    canonicalFullStep-GRUF4Norm-prefix-bridge
    canonical-gruf4-norm-watkins-prefix-composition-theorem
    FreeMonoidActionHomomorphism
    freeMonoidActionHomomorphism-from-square
    canonicalClock-freeMonoidActionHomomorphism
    ExactNatObservationSimulation
    noExactNatSimulation-through-finite-Int8
    canonicalNoExactTuringCounterObservation
    ContinuousLeftInverseTheorem
    canonicalRingStateInjective
    canonicalDenseNeighborhoodSeparation
    canonicalPigeonholeNatClockContradiction
    canonicalNoGlobalInt8DiscreteUAPOnOrbit
    canonicalNoNontrivialFiniteCycle-theorem
    canonicalDeterministicFiniteStepDivergenceInevitability
    canonicalNoFiniteStepConvergenceToFixedPoint
    CanonicalGlobalTokenConjugacyTheorem
    canonical-global-token-conjugacy
    CanonicalGlobalTokenLMCompositionTheorem
    canonical-global-token-lm-composition-theorem
    canonicalToken-prefix-monoid-homomorphism
    canonicalTokenLogitTrace-append
    canonicalTokenSparsemaxWeight-shared
    canonicalTokenSparsemaxPolicy-shared
    canonicalTokenSparsemaxTrace-append
    CanonicalExactRNNLMTheorem
    canonical-exact-rnn-lm-theorem
    CanonicalIntegerHaarScaledOrthogonalityTheorem
    canonical-integer-haar-scaled-orthogonality-theorem
    CanonicalAStarCostGuidanceTheorem
    canonical-a-star-cost-guidance-theorem
    CanonicalLinearHaarSparsemaxAttentionCompositionTheorem
    canonical-linear-haar-sparsemax-attention-composition-theorem
    CanonicalFullStateHaarSparsemaxInvariantCompositionTheorem
    canonical-full-state-haar-sparsemax-invariant-composition-theorem
    BairdSevenStarProblem
    bairdSevenStar
    NonIIDMarkovWalrasianProblem
    nonIIDMarkovStationaryWalrasian-lift
    Majority3ShapleyEquilibrium
    majority3ShapleyEquilibriumWitness
    '
    while IFS= read -r symbol; do
      [ -z "$symbol" ] || grep -Fq "$symbol" "$theorem" || { echo "missing theorem symbol: $symbol"; exit 1; }
    done <<< "$required"
    [ ! -f .ci/discovery/learner_semantic_manifest.m ] || { echo "generated semantic lookup table present"; exit 1; }
    [ ! -f .ci/discovery/learner-semantic-laws.tsv ] || { echo "generated semantic law artifact present"; exit 1; }
    grep -Eiq 'walsh|rope|target-network|target_network|target network|normalization|regularization' "$learner" && { echo "forbidden semantic term present"; exit 1; } || true
    grep -Fq 'open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C' "$theorem" || { echo "non-canonical theorem source"; exit 1; }
    ''
  else if lane == "surface" then
    ''
    set -euo pipefail
    count=$(git ls-files '*Monolith.agda' | wc -l)
    [ "$count" -eq 2 ] || { echo "expected exactly two Agda monoliths, found $count"; exit 1; }
    [ -f .ci/actions_ci.dhall ] || { echo "missing Dhall orchestrator"; exit 1; }
    ! git ls-files '*.roc' | grep -q . || { echo "Roc source remains"; exit 1; }
    forbidden='\.sh$|\.bash$|\.zsh$|\.fish$|\.cmd$|\.bat$|\.ps1$|\.command$|\.py$|\.java$|\.kt$|\.scala$|\.groovy$|\.clj$|\.cljs$|\.js$|\.mjs$|\.cjs$|\.ts$|\.tsx$|\.elm$|\.purs$|\.hs$|\.lhs$|\.cabal$|\.lua$|\.nim$|\.nims$|\.rocx$|\.ml$|\.mli$|\.sml$|\.c$|\.h$|\.cc$|\.cpp$|\.cxx$|\.hpp$|\.hxx$|\.cs$|\.fs$|\.fsx$|\.vb$|\.csproj$|\.fsproj$|\.vbproj$|\.sln$|\.html$|\.htm$|\.css$|\.tex$|\.ltx$|\.sty$|\.cls$|\.bib$|\.scm$|\.scheme$|\.ss$|\.rkt$'
    ! git ls-files | grep -E "$forbidden" || { echo "forbidden source suffix present"; exit 1; }
    retired='guix|guile|scheme|evolutionary-search|evolutionary algorithm|sparsemax2pair|fixedtemperaturesparsemax|actionscore|policyleftweight|tsts|gresher'
    ! git ls-files -z | xargs -0 grep -Eil "$retired" 2>/dev/null | grep -q . || { echo "retired term present"; exit 1; }
    ''
  else if lane == "versions" then
    ''
    set -euo pipefail
    "$AGDA_COMMAND" --version
    mmc --version
    dhall --version
    ''
  else if lane == "all" then
    ''
    set -euo pipefail
    "$AGDA_COMMAND" --version
    mmc --version
    dhall --version
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    mmc --make .ci/check_forbidden_theorems
    ./.ci/check_forbidden_theorems
    mmc --make .ci/discovery/theorem_monolith_egraph_sync
    ./.ci/discovery/theorem_monolith_egraph_sync
    mmc --make .ci/discovery/symbolic_egraph_test
    ./.ci/discovery/symbolic_egraph_test
    mmc --make .ci/discovery/interpolated_theorem_egraph_test
    ./.ci/discovery/interpolated_theorem_egraph_test
    ''
  else
    ''
    echo "unknown CI lane: $CI_LANE"
    exit 2
    ''

in script
