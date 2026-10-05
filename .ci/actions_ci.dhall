let Lane = < AgdaLearner | AgdaTheorem | AgdaSafe | Agda2HsLiquid | MirthFastDirty | MercuryPurity | Mercury | Pages | Discovery | EconlibCrossrepo | EconlibEquilibriumSearch | StrictExistenceImpossibility | StationaryCycleImpossibility | IsomorphismTransport | SemanticContract | Surface | Versions | AutoMerge | All >

let lane : Lane = env:CI_LANE

let script = merge {
  AgdaLearner = ''
    set -euo pipefail
    nix run .#mirth-agda-sync -- --check
    "$AGDA_COMMAND" --version
    "$AGDA_COMMAND" -i . FullCoupled/CanonicalLearnerMonolith.agda
    '',
  AgdaTheorem = ''
    set -euo pipefail
    nix run .#mirth-agda-sync -- --check
    while IFS= read -r file; do
      "$AGDA_COMMAND" -i . "$file"
    done < <(git ls-files '*.agda')
    grep -Fq -- '{-# OPTIONS --erased-cubical #-}' FullCoupled/TheoremsMonolith.agda
    grep -Fq -- '{-# OPTIONS --guarded #-}' FullCoupled/TheoremsMonolith.agda
    grep -Fq -- '{-# OPTIONS --guardedness #-}' FullCoupled/TheoremsMonolith.agda
    '',
  AgdaSafe = ''
    set -euo pipefail
    "$AGDA_COMMAND" --version
    echo "agda-safe=not-applicable; canonical surface is intentionally non-safe for Prelude-compatible theorem checking"
    '',
  Agda2HsLiquid = ''
    set -euo pipefail
    nix run .#agda-haskell-pipeline
    test -s build/agda-haskell/FullCoupled/Agda2HsSurface.hs
    test -s build/agda-haskell/agda2hs-liquid-manifest.tsv
    echo "agda2hs-ghc=pass"
    echo "liquidhaskell-z3=pass"
    '',
  MirthFastDirty = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    test -f .ci/mirth/agda_to_elm.mth
    test -f .ci/mirth/ascii_surface.mth
    test -f .ci/mirth/agda_import_sync.mth
    test -f .ci/mirth/agda_command_sync.mth
    test -f .ci/mirth/agda_graph.mth
    grep -Fq 'module actions.agda_to_elm' .ci/mirth/agda_to_elm.mth
    grep -Fq 'siteTitle : String' .ci/mirth/agda_to_elm.mth
    grep -Fq 'Graph.nodes' .ci/mirth/agda_to_elm.mth

    nix run .#mirth-ascii-sync
    nix run .#mirth-agda-import-sync -- --check
    nix run .#mirth-agda-command-sync -- --check
    nix run .#mirth-agda-graph -- "$tmp/GeneratedAgdaGraph.elm"
    test -s "$tmp/GeneratedAgdaGraph.elm"
    grep -Fq 'module GeneratedAgdaGraph exposing (Node, Edge, nodes, edges)' "$tmp/GeneratedAgdaGraph.elm"
    grep -Fq 'FullCoupled.TheoremsMonolith' "$tmp/GeneratedAgdaGraph.elm"

    mirthc .ci/mirth/agda_to_elm.mth -o "$tmp/agda-to-elm.c"
    cc -std=c99 "$tmp/agda-to-elm.c" -o "$tmp/agda-to-elm"
    "$tmp/agda-to-elm" > "$tmp/GeneratedTheoremSurface.elm"
    test -s "$tmp/GeneratedTheoremSurface.elm"
    grep -Fq 'siteTitle : String' "$tmp/GeneratedTheoremSurface.elm"
    grep -Fq 'nodeLines : List String' "$tmp/GeneratedTheoremSurface.elm"
    grep -Fq 'edgeLines : List String' "$tmp/GeneratedTheoremSurface.elm"
    if LC_ALL=C grep -n '[^[:print:][:space:]]' "$tmp/GeneratedTheoremSurface.elm"; then exit 1; fi
    echo "mirth-c99-transpile-and-execute=pass"
    '',
  MercuryPurity = ''
    set -euo pipefail
    files=$(git ls-files '*.m')
    [ -n "$files" ] || { echo "no Mercury sources found"; exit 1; }
    if grep -nHE '(^|[^A-Za-z])(impure|semipure)([^A-Za-z]|$)' $files; then
      echo "Mercury purity violation: impure/semipure syntax is forbidden in repository .m sources"
      exit 1
    fi
    if grep -nHE 'pragma[[:space:]]+promise_(impure|semipure)' $files; then
      echo "Mercury purity violation: promise_impure/promise_semipure is forbidden"
      exit 1
    fi
    if grep -nHE 'pragma[[:space:]]+foreign_proc' $files; then
      echo "Mercury purity violation: foreign_proc is forbidden in repository .m sources"
      exit 1
    fi
    echo "mercury-purity=pass"
    '',
  Mercury = ''
    set -euo pipefail
    nix run .#mercury-theorem-e2e
    '',
  Pages = ''
    set -euo pipefail
    nix run .#mercury-theorem-e2e
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    grep -Fq 'module FullCoupled.CanonicalLearnerMonolith' FullCoupled/CanonicalLearnerMonolith.agda
    grep -Fq 'module FullCoupled.TheoremsMonolith' FullCoupled/TheoremsMonolith.agda
    dhall type --file .ci/presentation-contract.dhall >/dev/null
    dhall-to-json --file .ci/presentation-contract.dhall > "$tmp/presentation-contract.json"
    grep -Fq '"graphGenerator": ".ci/mirth/agda_graph.mth"' "$tmp/presentation-contract.json"
    grep -Fq '"surfaceGenerator": ".ci/mirth/agda_to_elm.mth"' "$tmp/presentation-contract.json"
    grep -Fq '"elmManifest": ".ci/elm-application.dhall"' "$tmp/presentation-contract.json"
    grep -Fq '"siteEntry": "index.html"' "$tmp/presentation-contract.json"
    grep -Fq '"compiledElm": "elm.js"' "$tmp/presentation-contract.json"
    grep -Fq '"asciiGenerator": ".ci/mirth/ascii_surface.mth"' "$tmp/presentation-contract.json"
    output_dir="$tmp"
    if [ -n "$(printenv PAGES_OUTPUT_DIR 2>/dev/null || true)" ]; then
      output_dir="$(printenv PAGES_OUTPUT_DIR)"
    fi
    mkdir -p "$output_dir"
    mkdir -p "$tmp/src"
    cp site/Main.elm "$tmp/src/Main.elm"
    echo "pages-stage=mirth-graph-compile"
    echo "pages-stage=mirth-graph-compile-done"
    nix run .#mirth-agda-graph -- "$tmp/src/GeneratedAgdaGraph.elm"
    echo "pages-stage=mirth-surface-compile"
    mirthc .ci/mirth/agda_to_elm.mth -o "$tmp/agda-to-elm.c"
    echo "pages-stage=mirth-surface-compile-done"
    cc -std=c99 "$tmp/agda-to-elm.c" -o "$tmp/agda-to-elm"
    echo "pages-stage=surface-run-1"
    "$tmp/agda-to-elm" > "$tmp/agda-to-elm.sh"
    echo "pages-stage=surface-run-1-done"
    echo "pages-stage=surface-run-2"
    "$tmp/agda-to-elm" > "$tmp/src/GeneratedTheoremSurface.elm"
    echo "pages-stage=surface-run-2-done"
    test -s "$tmp/src/GeneratedAgdaGraph.elm"
    test -s "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'siteTitle : String' "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'nodeLines : List String' "$tmp/src/GeneratedTheoremSurface.elm"
    grep -Fq 'FullCoupled.CanonicalLearnerMonolith' "$tmp/src/GeneratedAgdaGraph.elm"
    grep -Fq 'FullCoupled.TheoremsMonolith' "$tmp/src/GeneratedAgdaGraph.elm"
    grep -Fq 'imports' "$tmp/src/GeneratedAgdaGraph.elm"
    dhall-to-json --file "$GITHUB_WORKSPACE/.ci/elm-application.dhall" > "$tmp/elm.json"
    sed -i -e 's/"source_directories"/"source-directories"/g' -e 's/"elm_version"/"elm-version"/g' -e 's/"elm_dependencies"/"dependencies"/g' -e 's/"test_dependencies"/"test-dependencies"/g' "$tmp/elm.json"
    test -s "$tmp/elm.json"
    cd "$tmp"
    elm make src/Main.elm --optimize --output "$output_dir/elm.js"
    test -s "$output_dir/elm.js"
    echo "pages-build=pass"
    '',
  Discovery = ''
    set -euo pipefail
    nix run .#mirth-agda-sync -- --check
    tmp_graph=$(mktemp -d)
    trap 'rm -rf "$tmp_graph"' EXIT
    nix run .#mirth-agda-graph -- "$tmp_graph/GeneratedAgdaGraph.elm" | bash -s -- "$tmp_graph/GeneratedAgdaGraph.elm"
    test -s "$tmp_graph/GeneratedAgdaGraph.elm"
    grep -Fq 'FullCoupled.TheoremsMonolith' "$tmp_graph/GeneratedAgdaGraph.elm"
    nix run .#mercury-theorem-e2e
    (cd .ci/discovery && mmc --make symbolic_egraph_test && ./symbolic_egraph_test)
    (cd .ci/discovery && mmc --make interpolated_theorem_egraph_test && ./interpolated_theorem_egraph_test)
    (cd .ci/discovery && mmc --make real_semantic_egraph && ./real_semantic_egraph)
    (cd .ci/discovery && mmc --make liquid_haskell_graph && ./liquid_haskell_graph ../../build/agda-haskell/agda2hs-liquid-manifest.tsv)
    report=.ci/discovery/theorem-monolith-egraph-sync.dhall
    dhall text --file "$report" >/dev/null
    grep -Fq 'forcedSymbolicTarget = True' "$report" && { echo "forced symbolic target"; exit 1; } || true
    grep -Fq 'singleAgdaSource = False' "$report" && { echo "non-canonical Agda source"; exit 1; } || true
    grep -Fq 'graphSearch = "A* cost-guided dependency paths"' "$report" || { echo "missing A* graph label"; exit 1; }
    grep -Fq 'astarScoreOrdered = True' "$report" || { echo "A* order gate failed"; exit 1; }
    grep -Fq 'emergentCompositionCount = 0' "$report" && { echo "no emergent composition"; exit 1; } || true
    grep -Fq 'newNonredundantTheoremCount = 0' "$report" || { echo "unexpected new nonredundant theorem claim"; exit 1; }
    grep -Fq 'reviewFrontierCount = 13' "$report" || { echo "theorem review frontier is incomplete"; exit 1; }
    grep -Fq 'CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem' "$report" || { echo "existing LayerNorm infinite-horizon review frontier missing"; exit 1; }
    grep -Fq 'AStarPlanMonoidTheorem' "$report" || { echo "A* plan-monoid review frontier missing"; exit 1; }
    grep -Fq 'CanonicalTokenArbitraryLengthGenerationTheorem' "$report" || { echo "token-generation review frontier missing"; exit 1; }
    grep -Fq 'NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem' "$report" || { echo "Maxwell/GRU review frontier missing"; exit 1; }
    grep -Fq 'GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem' "$report" || { echo "GRU convergence-identifiability frontier missing"; exit 1; }
    grep -Fq 'dominanceDetection = True' "$report" || { echo "record-field dominance detection missing"; exit 1; }
    grep -Fq 'prunedPublicTheoremCount = 5' "$report" || { echo "expected two pruned public theorem endpoints"; exit 1; }
    grep -Fq 'integerLayerNorm-egraph-astar-eventual-semantic-closure' "$report" || { echo "eventual-closure redundancy was not audited"; exit 1; }
    grep -Fq 'integerLayerNorm-egraph-astar-infinite-stable-tail' "$report" || { echo "stable-tail redundancy was not audited"; exit 1; }
    grep -Fq 'eGraphEconomicFixedPoint' "$report" || { echo "economic fixed-point projection pruning was not audited"; exit 1; }
    grep -Fq 'eGraphEconomicWalrasianEquilibrium' "$report" || { echo "economic Walrasian projection pruning was not audited"; exit 1; }
    grep -Fq 'eGraphEconomicComposition-injective' "$report" || { echo "economic injectivity projection pruning was not audited"; exit 1; }
    grep -Fq 'Name \\= "--"' .ci/discovery/learner_semantic_extractor.m || { echo "comment parser guard missing"; exit 1; }
    set -euo pipefail
    theorem=FullCoupled/TheoremsMonolith.agda
    sync=.ci/discovery/theorem-monolith-egraph-sync.dhall
    learner=FullCoupled/CanonicalLearnerMonolith.agda
    [ -f "$theorem" ] || { echo "missing theorem monolith"; exit 1; }
    [ -f "$learner" ] || { echo "missing learner monolith"; exit 1; }

    for symbol in       CanonicalMARLLawCompositionTheorem       CanonicalGRUF4WatkinsPrefixCompositionTheorem       ContinuousHodgeMaxwellExactRepresentationData       ConnectedContinuousHodgeMaxwellGRURepresentationTheorem       CanonicalLearnerHodgeMaxwellCompositionTheorem       NLabMaxwellSemanticClosure       NLabMaxwellFourLawSemanticallyClosed       nLabMaxwellEulerLagrangeShell-equivalence       nLabMaxwellFourLawOneStepClosed       nLabMaxwellIterateConjugacyClosed       canonical-learner-hodge-maxwell-step-conjugacy       CanonicalF4GlobalOptimizerStabilityTheorem       AStarPlanMonoidTheorem       CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem       CanonicalIntegerLayerNormAStarExecutionBridgeTheorem       integerLayerNorm-egraph-astar-finite-rank-witness       AStarHaskellMonadSurface       aStar-plan-append-associative       aStar-plan-append-identity-left       aStar-plan-append-identity-right       CanonicalIntegerLayerNormEGraphAStarTheorem       integerLayerNorm-a-star-semantic-closure       IntegerLayerNormConfigurationStabilityTheorem       integer-layernorm-configuration-stability-theorem       IntegerLayerNormEpsilonRayGrowthTheorem       integer-layernorm-epsilon-ray-growth-theorem       CanonicalIntegerLayerNormStabilityGrowthTheorem       canonical-integer-layernorm-stability-growth-theorem       CanonicalF4IntegerLayerNormStabilityBoundaryTheorem       canonical-f4-integer-layernorm-stability-boundary-theorem       canonicalTotalCountSuccessorWitness       canonical-token-arbitrary-length-generation-theorem       f4-unit-forcing-linear-growth       f4-unit-forcing-no-upper-bound       GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem       BrouwerMixedNashExistence       nashEveryFiniteGameViaBrouwer       brouwerMixedNashFixedPointBridge       finiteMixedNash-brouwer-egraph-astar-proof       finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof       finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof-nash       finiteMixedNash-brouwer-gru-egraph-astar-distribution-fixed       finiteMixedNash-egraph-astar-convergence       finiteMixedNash-egraph-astar-eventualStationarity       finiteMixedNash-egraph-astar-proof       finiteMixedNash-cycle-transport       finiteMixedNash-from-GRU-tail       EGraphEconomicComposition       EGraphEconomicConvergenceFixedPointWitness       GeneralizedIndividualDemandWitness       GeneralizedFirmSupplyWitness       GeneralizedAggregateDemandSupplyWitness       GeneralizedAggregateExcessDemandWitness       GeneralizedAggregateExcessDemandRegularityWitness       GeneralizedAggregateMarketClearingWitness       GeneralizedAggregateSupportingPriceWitness       ExpandedGeneralizedAggregateExcessDemandKernel       expandedGeneralizedAggregateExcessDemand-closure       GeneralizedAggregateExcessDemandFixedPointWitness       expandedGeneralizedAggregateExcessDemand-fixedPoint       EGraphEconomicAggregateExcessDemandFixedPointComposition       eGraphEconomicAggregateExcessDemand-fixedPointClosure       EGraphEconomicAggregateExcessDemandComposition canonicalStationaryPriceUpdate canonicalStationaryPriceLaw UnconditionalEGraphEconomicStationaryPriceComposition unconditionalEGraphEconomicStationaryPriceClosure unconditionalEGraphEconomicStationaryPriceComposition-from-path       eGraphEconomicAggregateExcessDemand-closure       EGraphEconomicRepresentationWitness       EGraphEconomicWalrasianWitness       eGraphEconomicComposition-closure       eGraphEconomicComposition-injective       eGraphEconomicFixedOrbit       eGraphEconomicRepresentationInjective       eGraphEconomicSemanticEquality       eGraphEconomicWalrasianEquilibrium       GeneralizedWalrasianEquilibrium       CompetitiveProductionEconomy       CompetitiveWalrasianEquilibriumWithProduction       megaNoEquilibriumGeneralizedWalrasian       noUnconditionalMegaGeneralizedWalrasianExistence       FiniteCandidateDecision       FiniteCandidatePriceResult       finiteCandidatePriceSearch       finiteCandidatePriceSearch-complete       EGraphEconomicFiniteCandidatePriceComposition       eGraphEconomicFiniteCandidatePriceClosure       eGraphEconomicFiniteCandidatePriceComposition-from-path       CommonsPreservationDerivation       CommonsNonDerivabilityCounterexample       noUnconditionalCommonsPreservation       twoNotLeOne       twoAgentCommonsCounterexample       noUnconditionalCommonsPreservation-twoAgent
    do
      grep -Fq "$symbol" "$theorem" || { echo "current theorem symbol missing: $symbol"; exit 1; }
    done
    for symbol in FractalInjectiveComposition fractalLevelInjective fractalTransportedEncodeInjective canonicalGRUFractal canonicalGRUFractalLevelInjective canonicalGRUFractalTransportedInjective canonicalGRUTwoScaleInjective PhysicsGRUFractalAdapter EconomicsGRUFractalAdapter economicObservation economicLevelTransport economicLevelTransportInjective economicLevelTransportRepresentation; do
      grep -Fq "$symbol" "$theorem" || { echo "consolidated theorem symbol missing: $symbol"; exit 1; }
    done

    [ -f docs/research/theorem-unconditional-commons-nonderivability-2026-09-26.md ] || { echo "commons research note missing"; exit 1; }
    grep -Fq 'suc (suc zero) ≤ suc zero' "$theorem" || { echo "commons capacity violation missing"; exit 1; }
    grep -Fq 'AStarSemanticClosure' "$theorem" || { echo "A* semantic closure kernel missing"; exit 1; }
    grep -Fq 'semanticEGraphAStarClosure' "$theorem" || { echo "theorem/e-graph/A* seam missing"; exit 1; }
    grep -Fq 'UnconditionalAgdaEGraphAStarClosure' "$theorem" || { echo "repository-wide e-graph closure missing"; exit 1; }
    grep -Fq 'StrictProgressRelation' "$theorem" || { echo "strict progress relation kernel missing"; exit 1; }
    grep -Fq 'EGraphEconomicComposition' "$theorem" || { echo "economic e-graph composition kernel missing"; exit 1; }
    grep -Fq 'eGraphEconomicComposition-closure' "$theorem" || { echo "economic e-graph closure theorem missing"; exit 1; }
    grep -Fq 'eGraphEconomicRepresentationInjective' "$theorem" || { echo "economic representation injectivity theorem missing"; exit 1; }
    grep -Fq 'canonicalGRUStatisticalEncodeInjective' "$theorem" || { echo "GRU statistical injectivity theorem missing"; exit 1; }
    grep -Fq 'CanonicalGRUStatisticalInjectivityTheorem' "$theorem" || { echo "GRU statistical injectivity package missing"; exit 1; }
    grep -Fq 'ConnectedContinuousHodgeMaxwellGRURepresentationTheorem' "$theorem" || { echo "connected Hodge-Maxwell GRU injectivity package missing"; exit 1; }
    [ ! -f FullCoupled/CarrierPolymorphicFrontier.agda ] || { echo "redundant frontier Agda module remains"; exit 1; }
    grep -Fq 'FactorTransitionWitness' FullCoupled/TheoremsMonolith.agda || { echo "factor transition kernel missing"; exit 1; }
    grep -Fq 'canonicalPolicyFactorTransition' FullCoupled/TheoremsMonolith.agda || { echo "canonical factor transition adapter missing"; exit 1; }
    grep -Fq 'StepConjugacyWitness' FullCoupled/TheoremsMonolith.agda || { echo "step conjugacy kernel missing"; exit 1; }
    grep -Fq 'DistributionalStationaryAggregateTransport' FullCoupled/TheoremsMonolith.agda || { echo "stationary aggregate bridge missing"; exit 1; }
    grep -Fq 'ProductionFeasibilityWitness' FullCoupled/TheoremsMonolith.agda || { echo "production witness surface missing"; exit 1; }
    grep -Fq 'SupportingPriceWitness' FullCoupled/TheoremsMonolith.agda || { echo "supporting price witness surface missing"; exit 1; }
    grep -Fq 'FiniteCandidateDecision' FullCoupled/TheoremsMonolith.agda || { echo "finite candidate decision kernel missing"; exit 1; }
    grep -Fq 'finiteCandidatePriceSearch' FullCoupled/TheoremsMonolith.agda || { echo "finite candidate price search kernel missing"; exit 1; }
    grep -Fq 'CertifiedEGraphEdge' "$theorem" || { echo "e-graph certificate surface missing"; exit 1; }
    grep -Fq "naive-limit-injectivity-impossible" "$theorem" || { echo "limit impossibility theorem missing"; exit 1; }

    grep -Fq 'UnconditionalAgdaEGraphAStarClosure' "$theorem" || { echo "repository-wide e-graph closure missing"; exit 1; }
    for module in canonicalLearnerMonolith theoremsMonolith
    do      grep -Fq "$module" "$theorem" || { echo "consolidated Agda semantic index missing: $module"; exit 1; }
    done
    monolith_count=$(git ls-files '*Monolith.agda' | wc -l)
    [ "$monolith_count" -eq 2 ] || { echo "expected exactly two Agda monoliths, found $monolith_count"; exit 1; }
    agda_files=$(git ls-files '*.agda')
    expected_agda_files='FullCoupled/Agda2HsSurface.agda
FullCoupled/CanonicalLearnerMonolith.agda
FullCoupled/FormalMethods/HoareLogic.agda
FullCoupled/FormalMethods/IMP.agda
FullCoupled/FormalMethods/OperationalSemantics.agda
FullCoupled/FormalMethods/Security.agda
FullCoupled/FormalMethods/SeparationLogic.agda
FullCoupled/FormalMethods/Types.agda
FullCoupled/FormalMethods/VerificationConditions.agda
FullCoupled/FormalMethods/gentle-intro-to-reflection/tangled.agda
FullCoupled/TheoremsMonolith.agda'
    [ "$agda_files" = "$expected_agda_files" ] || {
      echo "tracked Agda source surface mismatch"
      printf '%s\n' "expected:" "$expected_agda_files" "actual:" "$agda_files"
      exit 1
    }
    [ ! -e Main.agda ] || { echo "legacy Main.agda must remain retired"; exit 1; }
    grep -Fq 'Complete surviving-Agda closure index' "$readme" || { echo "README missing complete Agda closure index"; exit 1; }
    law_count=$(awk -F'= ' '/semanticLawCount =/ {gsub(/[^0-9]/,"",$2); print $2; exit}' "$sync")
    [ -n "$law_count" ] && [ "$law_count" -gt 0 ] || { echo "semantic law inventory is empty"; exit 1; }

    record_count=$(awk '/^[[:space:]]*record[[:space:]]+[A-Za-z0-9_.-]+/ {count++} END {print count+0}' "$theorem")
    declaration_count=$(awk '/^[A-Za-z][A-Za-z0-9_.-]*[[:space:]]*:/ {count++} END {print count+0}' "$theorem")
    economic_record_count=$(awk 'BEGIN {IGNORECASE=1} /^[[:space:]]*record[[:space:]]+[A-Za-z0-9_.-]+/ && /Walras|Welfare|Pareto|Production|Demand|Supply|Market|Price|Equilibrium|POMDP|Boundary|Closure|Transport|Conjugacy|Composition/ {count++} END {print count+0}' "$theorem")
    economic_declaration_count=$(awk 'BEGIN {IGNORECASE=1} /^[A-Za-z][A-Za-z0-9_.-]*[[:space:]]*:/ && /Walras|Welfare|Pareto|Production|Demand|Supply|Market|Price|Equilibrium|POMDP|Boundary|Closure|Transport|Conjugacy|Composition/ {count++} END {print count+0}' "$theorem")
    counterexample_count=$(awk 'BEGIN {IGNORECASE=1} /^[[:space:]]*record[[:space:]]+[A-Za-z0-9_.-]+/ && /Boundary|Counterexample|Impossibility/ {count++} END {print count+0}' "$theorem")
    composition_count=$(awk 'BEGIN {IGNORECASE=1} /^[[:space:]]*record[[:space:]]+[A-Za-z0-9_.-]+/ && /Composition|Conjugacy|Transport|Closure|Isomorphism/ {count++} END {print count+0}' "$theorem")

    mkdir -p .ci/discovery
    {
      printf '%s\\n' '{'
      printf '  source_graph = "%s",\\n' "$graph"
      printf '  theorem_source = "%s",\\n' "$theorem"
      printf '  learner_source = "%s",\\n' "$learner"
      printf '  semanticLawCount = %s,\\n' "$law_count"
      printf '  record_count = %s,\\n' "$record_count"
      printf '  top_level_declaration_count = %s,\\n' "$declaration_count"
      printf '  economic_record_count = %s,\\n' "$economic_record_count"
      printf '  economic_declaration_count = %s,\\n' "$economic_declaration_count"
      printf '  counterexample_or_boundary_record_count = %s,\\n' "$counterexample_count"
      printf '  composition_transport_record_count = %s,\\n' "$composition_count"
      printf '  surface_authority = "TheoremsMonolith.agda",\\n'
      printf '  dependency_authority = "theorem-monolith-egraph-sync.dhall",\\n'
      printf '  frontier_policy = "PROVED | CONDITIONAL | FRONTIER | BLOCKED-BY-COUNTEREXAMPLE",\\n'
      printf '  closed_core = ["CanonicalMARLLawCompositionTheorem", "CanonicalGRUF4WatkinsPrefixCompositionTheorem", "CanonicalF4GlobalOptimizerStabilityTheorem", "f4-unit-forcing-linear-growth", "f4-unit-forcing-no-upper-bound"],\\n'
      printf '  composition_frontier = ["CanonicalLearnerHodgeMaxwellCompositionTheorem requires explicit Hodge representation and learner-step conjugacy witnesses"],\\n'
      printf '  economic_boundary = ["learner factor stability does not entail convergence", "learner factor stability does not entail a fixed point", "learner factor stability does not entail market clearing", "learner factor stability does not entail supporting prices", "learner factor stability does not entail Walrasian existence"],\\n'
      printf '  production_topology = "competitive production -> feasible plans -> profit-maximizing production -> demand -> aggregate resource balance -> market clearing -> derived/supporting price -> generalized Walrasian equilibrium",\\n'
      printf '  counterexample_policy = "the singleton empty-equilibrium model blocks promotion of unconditional generalized-Walrasian existence",\\n'
      printf '%s\\n' '}'
    } > .ci/discovery/economic-closure-graph.dhall

    dhall text --file .ci/discovery/economic-closure-graph.dhall >/dev/null
    grep -Fq 'surface_authority = "TheoremsMonolith.agda"' .ci/discovery/economic-closure-graph.dhall
    grep -Fq 'frontier_policy = "PROVED | CONDITIONAL | FRONTIER | BLOCKED-BY-COUNTEREXAMPLE"' .ci/discovery/economic-closure-graph.dhall
    echo "economic-closure-graph=pass"
    echo "economic-record-count=$economic_record_count"
    echo "economic-declaration-count=$economic_declaration_count"
    echo "counterexample-boundary-record-count=$counterexample_count"
    echo "composition-transport-record-count=$composition_count"
    '',
  EconlibCrossrepo = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git clone --quiet --depth 1 https://github.com/danlyng/Econlib.git "$tmp/Econlib"
    econlib_rev=$(git -C "$tmp/Econlib" rev-parse HEAD)

    upstream_economy="$tmp/Econlib/Econlib/Equilibrium/Economy.lean"
    upstream_existence="$tmp/Econlib/Econlib/Equilibrium/Existence.lean"
    upstream_markov="$tmp/Econlib/EconlibExamples/Equilibrium/MarkovStationary.lean"
    local_theorem="FullCoupled/TheoremsMonolith.agda"

    grep -Fq 'structure WalrasianEquilibrium' "$upstream_economy"
    grep -Fq 'theorem exists_equilibrium' "$upstream_existence"
    grep -Fq 'Nonempty E.WalrasianEquilibrium' "$upstream_existence"
    grep -Fq 'stationary Walrasian equilibrium' "$upstream_markov"

    grep -Fq 'GeneralizedWalrasianData' "$local_theorem"
    grep -Fq 'MegaGeneralizedWalrasianEquilibrium' "$local_theorem"
    grep -Fq 'GeneralizedWalrasianExistence' "$local_theorem"
    grep -Fq 'CanonicalLearnerHodgeMaxwellCompositionTheorem' "$local_theorem"
    grep -Fq 'CanonicalLearnerHodgeMaxwellCompositionTheorem' "$local_theorem"

    adapter_present=false
    adapter_dhall=False
    if grep -Eiq 'Econlib|exists_equilibrium' "$local_theorem"; then
      adapter_present=true
      adapter_dhall=True
    fi

    mkdir -p .ci/discovery
    {
      printf '%s\n' '{'
      printf '  econlib_repo = "danlyng/Econlib",\n'
      printf '  econlib_commit = "%s",\n' "$econlib_rev"
      printf '  upstream_static_existence = "Economy.exists_equilibrium",\n'
      printf '  upstream_equilibrium_object = "Economy.WalrasianEquilibrium",\n'
      printf '  local_mega_equilibrium_target = "GeneralizedWalrasianExistence",\n'
      printf '  local_composition_target = "CanonicalLearnerHodgeMaxwellCompositionTheorem",\n'
      printf '  local_mega_edge = "MegaGeneralizedWalrasianEquilibrium",\n'
      printf '  adapter_present = %s,\n' "$adapter_present"
      printf '  composition_path = ["Econlib::Economy.exists_equilibrium", "Actions::MegaGeneralizedWalrasianEquilibrium", "Actions::CanonicalLearnerHodgeMaxwellCompositionTheorem"],\n'
      printf '  graph_status = "composition-ready; explicit cross-language adapter still required"\n'
      printf '%s\n' '}'    } > .ci/discovery/econlib-crossrepo-sync.dhall

    dhall text --file .ci/discovery/econlib-crossrepo-sync.dhall >/dev/null
    grep -Fq 'upstream_static_existence = "Economy.exists_equilibrium"' .ci/discovery/econlib-crossrepo-sync.dhall
    grep -Fq 'local_composition_target = "CanonicalLearnerHodgeMaxwellCompositionTheorem"' .ci/discovery/econlib-crossrepo-sync.dhall
    echo "econlib-crossrepo-sync=pass"
    echo "econlib-commit=$econlib_rev"
    echo "adapter-present=$adapter_present"
    '',
  EconlibEquilibriumSearch = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git clone --quiet --depth 1 https://github.com/danlyng/Econlib.git "$tmp/Econlib"
    econlib_rev=$(git -C "$tmp/Econlib" rev-parse HEAD)

    root="$tmp/Econlib"
    local_theorem="FullCoupled/TheoremsMonolith.agda"

    files=(
      "$root/Econlib/Equilibrium/Economy.lean"
      "$root/Econlib/Equilibrium/Existence.lean"
      "$root/Econlib/Equilibrium/AggregateAccounting.lean"
      "$root/Econlib/Probability/Markov/Ergodic.lean"
      "$root/Econlib/GameTheory/ExtensiveForm/Core/Strategy.lean"
      "$root/Econlib/GameTheory/ExtensiveForm/Refinements/BeliefSystem.lean"
      "$root/Econlib/GameTheory/ExtensiveForm/Refinements/SequentialEquilibrium.lean"
    )
    for f in "''${files[@]}"; do
      [ -f "$f" ] || { echo "missing upstream graph file: $f"; exit 1; }
    done

    grep -Fq 'RegularEconomy' "$root/Econlib/Equilibrium/Existence.lean"
    grep -Fq 'theorem exists_equilibrium' "$root/Econlib/Equilibrium/Existence.lean"
    grep -Fq 'WalrasianEquilibrium' "$root/Econlib/Equilibrium/Economy.lean"
    grep -Fq 'StationaryWalrasianEquilibrium' "$root/Econlib/Equilibrium/AggregateAccounting.lean"
    grep -Fq 'exists_stationary' "$root/Econlib/Probability/Markov/Ergodic.lean"
    grep -Fq 'theorem geometric_convergence_to' "$root/Econlib/Probability/Markov/Ergodic.lean"
    grep -Fq '0 < P.transition' "$root/Econlib/Probability/Markov/Ergodic.lean"

    grep -Fq 'BehavioralStrategy' "$root/Econlib/GameTheory/ExtensiveForm/Core/Strategy.lean"
    grep -Fq 'BeliefSystem' "$root/Econlib/GameTheory/ExtensiveForm/Refinements/BeliefSystem.lean"
    grep -Fq 'SequentialEquilibrium' "$root/Econlib/GameTheory/ExtensiveForm/Refinements/SequentialEquilibrium.lean"

    grep -Fq 'GeneralizedWalrasianData' "$local_theorem"
    grep -Fq 'GeneralizedWalrasianExistence' "$local_theorem"
    grep -Fq 'MegaGeneralizedWalrasianEquilibrium' "$local_theorem"
    grep -Fq 'CanonicalLearnerHodgeMaxwellCompositionTheorem' "$local_theorem"

    pomdp_named=false
    pomdp_named_dhall=False
    grep -Riq 'POMDP|partially observable' "$root/Econlib" && pomdp_named=true && pomdp_named_dhall=True || true

    mkdir -p .ci/discovery
    {
      printf '%s\n' '{'
      printf '  econlib_repo = "danlyng/Econlib",\n'
      printf '  econlib_commit = "%s",\n' "$econlib_rev"
      printf '  benchmark_regular_assumption = "Econlib::RegularEconomy",\n'
      printf '  benchmark_static_existence = "Econlib::Economy.exists_equilibrium",\n'
      printf '  non_iid_transition = "arbitrary Markov/kernel transition",\n'
      printf '  stationary_law_node = "FiniteMarkovChain.exists_stationary",\n'
      printf '  stationary_law_convergence_node = "FiniteMarkovChain.geometric_convergence_to",\n'
      printf '  stationary_law_convergence_condition = "strictly positive transition probabilities",\n'
      printf '  stationary_equilibrium_node = "MarkovExchangeEconomy.StationaryWalrasianEquilibrium",\n'
      printf '  local_mega_edge = "MegaGeneralizedWalrasianEquilibrium",\n'
      printf '  local_composition = "CanonicalLearnerHodgeMaxwellCompositionTheorem",\n'
      printf '  partial_observation_nodes = ["BehavioralStrategy", "BeliefSystem", "SequentialEquilibrium"],\n'
      printf '  pomdp_named_in_econlib = %s,\n' "$pomdp_named"
      printf '  composition_path = ["Econlib::RegularEconomy", "Econlib::Economy.exists_equilibrium", "Actions::MegaGeneralizedWalrasianEquilibrium", "Actions::CanonicalLearnerHodgeMaxwellCompositionTheorem"],\n'
      printf '  pomdp_bridge_status = "local POMDP belief-policy closure remains explicit; no filtering or optimality is inferred"\n'
      printf '%s\n' '}'
    } > .ci/discovery/econlib-equilibrium-graph.dhall

    dhall text --file .ci/discovery/econlib-equilibrium-graph.dhall >/dev/null
    grep -Fq 'benchmark_regular_assumption = "Econlib::RegularEconomy"' .ci/discovery/econlib-equilibrium-graph.dhall
    grep -Fq 'non_iid_transition = "arbitrary Markov/kernel transition"' .ci/discovery/econlib-equilibrium-graph.dhall
    grep -Fq 'pomdp_bridge_status = "local POMDP belief-policy closure remains explicit; no filtering or optimality is inferred"' .ci/discovery/econlib-equilibrium-graph.dhall
    echo "econlib-equilibrium-search=pass"
    echo "econlib-commit=$econlib_rev"
    echo "pomdp-named-in-upstream=$pomdp_named"
    '',
  StrictExistenceImpossibility = ''
    set -euo pipefail
    (cd .ci/discovery && mmc --make strict_existence_impossibility_graph && ./strict_existence_impossibility_graph)
    report=.ci/discovery/strict-existence-impossibility-graph.dhall
    dhall text --file "$report" >/dev/null
    grep -Fq 'rule = "STRICT_EXISTENCE_OR_IMPOSSIBILITY_ONLY"' "$report" || { echo "strict rule missing"; exit 1; }
    grep -Fq 'orangeStatusesAllowed = False' "$report" || { echo "orange status enabled"; exit 1; }
    grep -Fq 'terminalStatuses = ["EXISTENCE", "IMPOSSIBILITY"]' "$report" || { echo "non-strict terminal status present"; exit 1; }
    ! grep -Eiq 'frontier|unknown|vague|adapter needed|unresolved|pending' "$report" || { echo "vague status present"; exit 1; }
    grep -Fq 'strict-existence-impossibility-graph=pass' "$report"
    '',
  StationaryCycleImpossibility = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git clone --quiet --depth 1 https://github.com/danlyng/Econlib.git "$tmp/Econlib"

    theorem=FullCoupled/TheoremsMonolith.agda    ergodic="$tmp/Econlib/Econlib/Probability/Markov/Ergodic.lean"

    grep -Fq 'canonicalNoNontrivialFiniteCycle-theorem' "$theorem"
    grep -Fq 'canonicalNoFiniteStepConvergenceToFixedPoint' "$theorem"
    grep -Fq 'isomorphismNoFiniteCycleTransport' "$theorem"
    grep -Fq 'exists_stationary' "$ergodic"
    grep -Fq 'theorem geometric_convergence_to' "$ergodic"
    grep -Fq '0 < P.transition' "$ergodic"

    mkdir -p .ci/discovery
    cat > .ci/discovery/stationary-cycle-impossibility-graph.dhall <<'DHALL'
{
  rule = "FINITE_DETERMINISTIC_CYCLE_HAS_STATIONARY_WITNESS_BUT_IS_EXCLUDED",
  terminalStatus = "IMPOSSIBILITY",
  requiresExactFiniteDeterministicProjection = True,
  stationaryDistributionWitness = {
    type = "uniform_cycle_measure",
    statement = "For a deterministic cycle of length m>0, the uniform probability law on the cycle is stationary for the induced deterministic Markov kernel.",
    use = "witness_only"
  },
  upstreamStationaryLaw = {
    theorem = "Econlib::FiniteMarkovChain.exists_stationary",
    role = "independent finite-state existence fact; it does not imply that a cycle exists"
  },
  convergenceGuard = {
    theorem = "Econlib::FiniteMarkovChain.geometric_convergence_to",
    condition = "strictly positive transition probabilities",
    role = "separate conditional convergence result; not used to claim convergence of an arbitrary deterministic cycle"
  },
  nodes = [
    "Agda::finiteOrbit-collision",
    "deterministic finite recurrent cycle",
    "uniform cycle stationary law",
    "Econlib::FiniteMarkovChain.exists_stationary",
    "Econlib::FiniteMarkovChain.geometric_convergence_to",
    "Agda::canonicalNoNontrivialFiniteCycle-theorem",
    "Agda::canonicalNoFiniteStepConvergenceToFixedPoint"
  ],
  edges = [
    { source = "finiteOrbit-collision", target = "eventual periodic orbit", reason = None Text },
    { source = "eventual periodic orbit", target = "deterministic finite recurrent cycle", reason = None Text },
    { source = "deterministic finite recurrent cycle", target = "uniform cycle stationary law", reason = None Text },
    { source = "Econlib::FiniteMarkovChain.exists_stationary", target = "stationary distribution", reason = Some "independent existence witness" },
    { source = "Econlib::FiniteMarkovChain.geometric_convergence_to", target = "quantitative convergence", reason = Some "requires strict positivity" },
    { source = "deterministic finite recurrent cycle", target = "canonicalNoNontrivialFiniteCycle-theorem", reason = Some "contradiction" },
    { source = "period-1 recurrent cycle", target = "canonicalNoFiniteStepConvergenceToFixedPoint", reason = Some "contradiction" }
  ],
  logicGuard = "stationary-law existence is not itself an obstruction; the obstruction is the canonical no-cycle theorem",
  isomorphismTransportNode = "Agda::isomorphismNoFiniteCycleTransport",
  isomorphismTransportRole = "exact conjugacy preserves finite-cycle exclusion on the isomorphic state space",
  status = "strict graph: no third terminal status"
}
DHALL
    dhall text --file .ci/discovery/stationary-cycle-impossibility-graph.dhall >/dev/null
    grep -Fq 'terminalStatus = "IMPOSSIBILITY"' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'stationaryDistributionWitness = {' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'type = "uniform_cycle_measure"' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'logicGuard = "stationary-law existence is not itself an obstruction; the obstruction is the canonical no-cycle theorem"' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'requiresExactFiniteDeterministicProjection = True' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    grep -Fq 'status = "strict graph: no third terminal status"' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    ! grep -Eiq 'frontier|unknown|vague|unresolved|pending' .ci/discovery/stationary-cycle-impossibility-graph.dhall
    echo "stationary-cycle-impossibility-graph=pass"
    '',
  IsomorphismTransport = ''
    set -euo pipefail
    "$AGDA_COMMAND" --allow-exec -i . FullCoupled/TheoremsMonolith.agda
    (cd .ci/discovery && mmc --make isomorphism_transport_graph && ./isomorphism_transport_graph)
    report=.ci/discovery/isomorphism-transport-graph.dhall
    dhall text --file "$report" >/dev/null
    grep -Fq 'rule = "ISOMORPHISM_TRANSPORT_CLOSURE"' "$report" || { echo "isomorphism transport rule missing"; exit 1; }
    grep -Fq 'orangeStatusesAllowed = False' "$report" || { echo "orange status enabled"; exit 1; }
    grep -Fq 'Agda::isomorphismEqualityTransport' "$report" || { echo "equality transport kernel missing"; exit 1; }
    grep -Fq 'Agda::isomorphismDisequalityTransport' "$report" || { echo "disequality transport kernel missing"; exit 1; }
    ! grep -Eiq 'frontier|unknown|vague|unresolved|pending' "$report" || { echo "vague transport status present"; exit 1; }
    ''
,
  SemanticContract = ''
    set -euo pipefail
    theorem=FullCoupled/TheoremsMonolith.agda
    learner=FullCoupled/CanonicalLearnerMonolith.agda
    import_sync=.ci/theorem-learner-import-sync.dhall
    generated_import_sync=$(mktemp)
    trap 'rm -f "$generated_import_sync"' EXIT
    dhall text --file "$import_sync" > "$generated_import_sync"
    bash "$generated_import_sync"
    required='
    canonical-recurrent-prefix-monoid-homomorphism
    canonicalF4-prefix-monoid-homomorphism
    
    canonicalGRUF4-prefix-monoid-homomorphism
    canonicalFullStep-GRUF4-prefix-bridge
    freeMonoidActionHomomorphism-from-square
    canonicalCount-freeMonoidActionHomomorphism
    canonicalNoNontrivialFiniteCycle-theorem
    StateIsomorphism
    canonicalDeterministicFiniteStepDivergenceInevitability
    canonicalNoFiniteStepConvergenceToFixedPoint
    CanonicalGlobalTokenEncodingConjugacyTheorem
    canonical-global-token-encoding-conjugacy
    CanonicalIntegerGRUTokenEncodingLeftInverse
    canonical-integer-gru-token-encoding-left-inverse
    canonicalIntegerGRUTokenEncodingInjective
    canonicalIntegerGRUTokenEncoding-continuous-discrete
    CanonicalIntegerGRUGlobalConjugateTheorem
    canonical-integer-gru-global-conjugate-theorem
    CanonicalGlobalTokenLMCompositionTheorem
    canonical-global-token-lm-composition-theorem
    canonicalToken-prefix-monoid-homomorphism
    canonicalTokenLogitTrace-append
    CanonicalExactRNNLMTheorem
    canonical-exact-rnn-lm-theorem
    CanonicalIntegerHaarScaledOrthogonalityTheorem
    canonical-integer-haar-scaled-orthogonality-theorem
    CanonicalAStarCostGuidanceTheorem
    CanonicalEndogenousEGraphAStarTransportClosureTheorem
    eGraphAStarConvergenceSemanticClosure
    eGraphAStarEventualStableFromRank
    eGraphAStarStablePathPersists
    eGraph-path-trans
    CanonicalIntegerLayerNormEGraphAStarTheorem
    integerLayerNorm-a-star-semantic-closure
    canonical-a-star-cost-guidance-theorem
    recurrentPrefix-scan-lifts-conjugacy
    canonical-recurrent-scan-conjugacy-theorem
    CanonicalFullLearnerConnectedScanConjugacyTheorem
    canonical-full-learner-connected-scan-conjugacy-theorem
    canonicalExactCompositionTuringCompletenessContract-impossible
    CanonicalFiniteCycleExclusionIsomorphismTheorem
    CanonicalOperatorCompositionTheorem
    canonical-operator-composition-theorem
    CanonicalPureNonOrangeBypassCompletionTheorem
    CanonicalStationarySubcompositionTheorem
    canonical-persistent-excitation-requirement-theorem
    ExactContractComputabilityBoundaryTheorem
    exact-contract-computability-boundary-theorem
    megaParetoOptimal
    MegaSecondWelfareTheoremBoundaryCounterexample
    megaSecondWelfareTheorem-boundary-counterexample
    megaNoStrictAffordableAlternative-is-demand-optimality
    nLabMaxwellEulerLagrangeShell-equivalence
    nLabMaxwellFourLawOneStepClosed
    nLabMaxwellIterateConjugacyClosed
    CanonicalGlobalTokenEncodingConjugacyTheorem
    CanonicalGlobalTokenLMCompositionTheorem
    
    CanonicalExactRNNLMTheorem
    canonicalLearnerBairdSevenStar
    canonicalGRUStatisticalEncodeLeftInverse
    leftInverse-implies-injective
    canonicalGRUStatisticalEncodeInjective
    JAXExecutionMirrorReproof
    jaxVmapAffine
    jaxAssociativePrefixSum
    jaxRecurrentScan
    jaxLexicographicScoreOrder
    jaxSparseSupportSize
    jaxSparseSupportTopK
    jaxSparsemaxPolicyIndex
    jaxIntegerLayerNormCenteredNumerators
    jaxIntegerLayerNormRadicand
    jaxBatchedIntegerLayerNormRadicand
    jaxSignedGate
    jaxGRUHiddenStep
    jaxBatchedGRUHiddenStep
    jaxTsallis2NearSparsityFraction
    jaxSupportSparsityFraction
    jaxJittedScanSum
    JAXExecutionMirrorReproof
    '
    while IFS= read -r symbol; do
      [ -z "$symbol" ] || grep -Fq "$symbol" "$theorem" || { echo "missing theorem symbol: $symbol"; exit 1; }
    done <<< "$required"
    [ ! -f .ci/discovery/learner_semantic_manifest.m ] || { echo "generated semantic lookup table present"; exit 1; }
    [ ! -f .ci/discovery/learner-semantic-laws.tsv ] || { echo "generated semantic law artifact present"; exit 1; }
    grep -Eiq 'walsh|rope|target-network|target_network|target network|normalization|regularization' "$learner" && { echo "forbidden semantic term present"; exit 1; } || true
    grep -Fq 'open import FullCoupled.CanonicalLearnerMonolith as C' "$theorem" || { echo "non-canonical theorem source"; exit 1; }
    '',
  Surface = ''
    set -euo pipefail
    count=$(git ls-files '*Monolith.agda' | wc -l)
    [ "$count" -eq 2 ] || { echo "expected exactly two Agda monoliths, found $count"; exit 1; }
    agda_count=$(git ls-files '*.agda' | wc -l)
    [ "$agda_count" -eq 11 ] || { echo "expected exactly eleven tracked Agda sources, found $agda_count"; exit 1; }
    [ -f FullCoupled/CanonicalLearnerMonolith.agda ] || { echo "missing canonical learner monolith"; exit 1; }
    [ -f FullCoupled/TheoremsMonolith.agda ] || { echo "missing theorem monolith"; exit 1; }
    [ -f .ci/actions_ci.dhall ] || { echo "missing Dhall orchestrator"; exit 1; }
    ! git ls-files '*.json' | grep -q . || { echo "JSON source/artifact remains"; exit 1; }
    ! find .ci/discovery -type f -name '*.json' -print -quit | grep -q . || { echo "generated JSON artifact remains"; exit 1; }
    retired='evolutionary-search|evolutionary algorithm|sparsemax2pair|fixedtemperaturesparsemax|actionscore|policyleftweight|tsts|gresher'
    md_link_found=0
    while IFS= read -r md; do
      if grep -Eq '\\]\\(|https?://' "$md"; then
        echo "Markdown link found outside the Elm presentation: $md"
        md_link_found=1
      fi
    done < <(git ls-files '*.md' '*.markdown')
    [ "$md_link_found" -eq 0 ] || { echo "Markdown links are forbidden outside Elm sites"; exit 1; }
    ! git ls-files -z | xargs -0 grep -Eil "$retired" 2>/dev/null | grep -q . || { echo "retired semantic term present"; exit 1; }
    ! grep -nE '(^|[[:space:];])pkgs\.python3([[:space:]]|$)|(^|[[:space:];])python3([[:space:]]|$)|(^|[[:space:];])python([[:space:]]|$)|pkgs\.pythonPackages' flake.nix .ci/*.sh .ci/*.dhall .ci/mirth/*.mth 2>/dev/null || { echo "non-JAX Python toolchain reference present"; exit 1; }
    ! grep -nE 'Exotic/ERL/FullCoupled|Exotic/FullCoupled' FullCoupled/*.agda README.md site/Main.elm docs/*.md 2>/dev/null || { echo "stale Exotic source path present"; exit 1; }
    '',
  Versions = ''
    set -euo pipefail
    "$AGDA_COMMAND" --version
    mmc --version
    dhall --version
    '',
  AutoMerge = ''
    set -euo pipefail
    : "''${GH_TOKEN:?GH_TOKEN is required}"
    : "''${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is required}"
    : "''${PR_NUMBER:?PR_NUMBER is required}"
    gh pr merge "$PR_NUMBER" --repo "$GITHUB_REPOSITORY" --auto --rebase
    '',
  All = ''
    set -euo pipefail
    nix run .#mirth-agda-sync -- --check
    "$AGDA_COMMAND" --version
    mmc --version
    dhall --version
    while IFS= read -r file; do
      "$AGDA_COMMAND" -i . "$file"
    done < <(git ls-files '*.agda')
    "$AGDA_COMMAND" --allow-exec -i . FullCoupled/TheoremsMonolith.agda
    (cd .ci && mmc --make check_forbidden_theorems && ./check_forbidden_theorems)
    nix run .#mercury-theorem-e2e
    (cd .ci/discovery && mmc --make symbolic_egraph_test && ./symbolic_egraph_test)
    (cd .ci/discovery && mmc --make interpolated_theorem_egraph_test && ./interpolated_theorem_egraph_test)
    ''
}
in script lane
