let Lane = < AgdaLearner | AgdaTheorem | AgdaSafe | Mercury | Discovery | EconlibCrossrepo | EconlibEquilibriumSearch | StrictExistenceImpossibility | StationaryCycleImpossibility | IsomorphismTransport | SemanticContract | Surface | Versions | AutoMerge | All >

let lane = env:CI_LANE

let script = merge {
  AgdaLearner = ''
    set -euo pipefail
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    '',
  AgdaTheorem = ''
    set -euo pipefail
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/FourLawClosureImpossibility.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUStatisticalInjectivity.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CommonsComposition.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalDomainAdapters.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalLimitClosure.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalEGraphAStarLimitComposition.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalLimitDecoderSurvival.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/ZPFStatisticalRepresentation.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TsallisStatisticalRepresentation.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/RepositorySemanticEGraphClosure.agda
    '',
  AgdaSafe = ''
    set -euo pipefail
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/FourLawClosureImpossibility.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUStatisticalInjectivity.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CommonsComposition.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalDomainAdapters.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/ZPFStatisticalRepresentation.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TsallisStatisticalRepresentation.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/RepositorySemanticEGraphClosure.agda
    '',
  Mercury = ''
    set -euo pipefail
    (cd .ci && mmc --make check_forbidden_theorems && ./check_forbidden_theorems)
    (cd .ci/discovery && mmc --make theorem_registry_reconcile && ./theorem_registry_reconcile --check)
    '',
  Discovery = ''
    set -euo pipefail
    (cd .ci/discovery && mmc --make theorem_registry_reconcile && ./theorem_registry_reconcile --check)
    (cd .ci/discovery && mmc --make theorem_monolith_egraph_sync && ./theorem_monolith_egraph_sync)
    (cd .ci/discovery && mmc --make symbolic_egraph_test && ./symbolic_egraph_test)
    (cd .ci/discovery && mmc --make interpolated_theorem_egraph_test && ./interpolated_theorem_egraph_test)
    report=.ci/discovery/theorem-monolith-egraph-sync.json
    grep -Fq '"forced_symbolic_target": true' "$report" && { echo "forced symbolic target"; exit 1; } || true
    grep -Fq '"single_agda_source": false' "$report" && { echo "non-canonical Agda source"; exit 1; } || true
    grep -Fq '"graph_search": "A* cost-guided dependency paths"' "$report" || { echo "missing A* graph label"; exit 1; }
    grep -Fq '"astar_score_ordered": true' "$report" || { echo "A* order gate failed"; exit 1; }
    grep -Fq '"emergent_composition_count": 0' "$report" && { echo "no emergent composition"; exit 1; } || true
    grep -Fq 'Name \\= "--"' .ci/discovery/learner_semantic_extractor.m || { echo "comment parser guard missing"; exit 1; }
    set -euo pipefail
    graph=docs/research/current-semantic-emergence-2026-09-25.mmd
    theorem=Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    sync=.ci/discovery/theorem-monolith-egraph-sync.json
    learner=Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    readme=README.md
    [ -f "$graph" ] || { echo "missing current semantic emergence graph"; exit 1; }
    [ -f "$theorem" ] || { echo "missing theorem monolith"; exit 1; }
    [ -f "$learner" ] || { echo "missing learner monolith"; exit 1; }
    [ -f "$readme" ] || { echo "missing README"; exit 1; }
    [ -f .ci/readme-doc-sync.dhall ] || { echo "missing Dhall README documentation sync"; exit 1; }
    generated_readme_sync=$(mktemp)
    trap 'rm -f "$generated_readme_sync"' EXIT
    dhall text --file .ci/readme-doc-sync.dhall > "$generated_readme_sync"
    bash "$generated_readme_sync" --check || { echo "README GitHub-facing documentation index is stale"; exit 1; }

    for node in       "Canonical learner definitions"       "Four exact MARL-facing laws"       "CanonicalMARLLawCompositionTheorem (closed)"       "Exact recurrent scan / composition"       "NormPair quotient / factor transition"       "Exact F4 optimizer stability"       "F4 unit-forcing growth ray"       "No unconditional infinite-horizon F4 upper bound"       "Canonical F4 × NormPair unconditional factor stability"       "CanonicalGRUF4NormWatkinsPrefixCompositionTheorem (closed)"       "ContinuousHodgeMaxwellExactRepresentationData"       "ConnectedContinuousHodgeMaxwellGRURepresentationTheorem"       "CanonicalLearnerHodgeMaxwellCompositionTheorem (proof-relevant bridge)"       "Competitive production economy"       "Feasible firm production plans"       "Profit-maximizing production"       "Aggregate resource balance"       "Market clearing"       "Walrasian existence"
    do
      grep -Fq "$node" "$graph" || { echo "current graph node missing: $node"; exit 1; }
    done

    for symbol in       CanonicalMARLLawCompositionTheorem       CanonicalGRUF4NormWatkinsPrefixCompositionTheorem       ContinuousHodgeMaxwellExactRepresentationData       ConnectedContinuousHodgeMaxwellGRURepresentationTheorem       CanonicalLearnerHodgeMaxwellCompositionTheorem       NLabMaxwellSemanticClosure       NLabMaxwellFourLawSemanticallyClosed       nLabMaxwellEulerLagrangeShell-equivalence       nLabMaxwellFourLawOneStepClosed       nLabMaxwellIterateConjugacyClosed       canonical-learner-hodge-maxwell-step-conjugacy       CanonicalNormPairQuotientFactorTransitionTheorem       CanonicalF4GlobalOptimizerStabilityTheorem       CanonicalF4NormPairUnconditionalFactorStabilityTheorem       CanonicalF4NormPairIterateFactorStabilityTheorem       canonicalTotalCountSuccessorWitness       canonical-token-arbitrary-length-generation-theorem       f4-unit-forcing-linear-growth       f4-unit-forcing-no-upper-bound       GeneralizedWalrasianEquilibrium       CompetitiveProductionEconomy       CompetitiveWalrasianEquilibriumWithProduction       megaNoEquilibriumGeneralizedWalrasian       noUnconditionalMegaGeneralizedWalrasianExistence       noUnconditionalMegaWalrasianExistenceAfterF4NormPairFactorStability       FiniteCandidateDecision       FiniteCandidatePriceResult       finiteCandidatePriceSearch       finiteCandidatePriceSearch-complete       CommonsPreservationDerivation       CommonsNonDerivabilityCounterexample       noUnconditionalCommonsPreservation       twoNotLeOne       twoAgentCommonsCounterexample       noUnconditionalCommonsPreservation-twoAgent
    do
      grep -Fq "$symbol" "$theorem" || { echo "current theorem symbol missing: $symbol"; exit 1; }
    done
    for symbol in FractalInjectiveComposition fractalLevelInjective fractalTransportedEncodeInjective; do
      grep -Fq "$symbol" Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda || { echo "fractal kernel symbol missing: $symbol"; exit 1; }
    done
    for symbol in canonicalGRUFractal canonicalGRUFractalLevelInjective canonicalGRUFractalTransportedInjective canonicalGRUTwoScaleInjective; do
      grep -Fq "$symbol" Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda || { echo "canonical fractal symbol missing: $symbol"; exit 1; }
    done
    for symbol in PhysicsGRUFractalAdapter EconomicsGRUFractalAdapter economicObservation economicLevelTransport economicLevelTransportInjective economicLevelTransportRepresentation; do
      grep -Fq "$symbol" Exotic/ERL/FullCoupled/GRUFractalDomainAdapters.agda || { echo "domain adapter symbol missing: $symbol"; exit 1; }
    done
    [ -f .ci/discovery/gru-fractal-domain-adapters-2026-09-26.mmd ] || { echo "GRU fractal domain adapter graph missing"; exit 1; }

    grep -Fq 'does not entail' "$graph" || { echo "economic non-implication boundary missing"; exit 1; }
    grep -Fq 'independent economic hypotheses' "$graph" || { echo "economic assumption boundary missing"; exit 1; }
    [ -f docs/research/theorem-unconditional-commons-nonderivability-2026-09-26.md ] || { echo "commons research note missing"; exit 1; }
    [ -f .ci/discovery/commons-nonderivability-2026-09-26.mmd ] || { echo "commons discovery graph missing"; exit 1; }
    [ -f .ci/discovery/gru-fractal-injective-composition-2026-09-26.mmd ] || { echo "GRU fractal injective composition graph missing"; exit 1; }
    grep -Fq "GRU-injective fractal composition" .ci/discovery/gru-fractal-injective-composition-2026-09-26.mmd || { echo "GRU fractal composition graph missing injective node"; exit 1; }
    grep -Fq 'Two-unit aggregate extraction' .ci/discovery/commons-nonderivability-2026-09-26.mmd || { echo "commons depletion graph missing aggregate extraction"; exit 1; }
    grep -Fq 'suc (suc zero) ≤ suc zero' "$theorem" || { echo "commons capacity violation missing"; exit 1; }
    grep -Fq 'Canonical F4 × NormPair unconditional factor stability' "$readme" || { echo "README stale or missing current core"; exit 1; }
    grep -Fq 'Repository-wide semantic e-graph closure' "$readme" || { echo "README stale or missing e-graph closure"; exit 1; }
    grep -Fq 'AStarSemanticClosure' Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda || { echo "A* semantic closure kernel missing"; exit 1; }
    grep -Fq 'semanticEGraphAStarClosure' "$theorem" || { echo "theorem/e-graph/A* seam missing"; exit 1; }
    grep -Fq 'UnconditionalAgdaEGraphAStarClosure' Exotic/ERL/FullCoupled/RepositorySemanticEGraphClosure.agda || { echo "repository-wide e-graph closure missing"; exit 1; }
    grep -Fq 'StrictProgressRelation' "$theorem" || { echo "strict progress relation kernel missing"; exit 1; }
    [ ! -f Exotic/ERL/FullCoupled/CarrierPolymorphicFrontier.agda ] || { echo "redundant frontier Agda module remains"; exit 1; }
    grep -Fq 'FactorTransitionWitness' Exotic/ERL/FullCoupled/TheoremsMonolith.agda || { echo "factor transition kernel missing"; exit 1; }
    grep -Fq 'canonicalPolicyFactorTransition' Exotic/ERL/FullCoupled/TheoremsMonolith.agda || { echo "canonical factor transition adapter missing"; exit 1; }
    grep -Fq 'StepConjugacyWitness' Exotic/ERL/FullCoupled/TheoremsMonolith.agda || { echo "step conjugacy kernel missing"; exit 1; }
    grep -Fq 'DistributionalStationaryAggregateTransport' Exotic/ERL/FullCoupled/TheoremsMonolith.agda || { echo "stationary aggregate bridge missing"; exit 1; }
    grep -Fq 'ProductionFeasibilityWitness' Exotic/ERL/FullCoupled/TheoremsMonolith.agda || { echo "production witness surface missing"; exit 1; }
    grep -Fq 'SupportingPriceWitness' Exotic/ERL/FullCoupled/TheoremsMonolith.agda || { echo "supporting price witness surface missing"; exit 1; }
    grep -Fq 'FiniteCandidateDecision' Exotic/ERL/FullCoupled/TheoremsMonolith.agda || { echo "finite candidate decision kernel missing"; exit 1; }
    grep -Fq 'finiteCandidatePriceSearch' Exotic/ERL/FullCoupled/TheoremsMonolith.agda || { echo "finite candidate price search kernel missing"; exit 1; }
    [ -f docs/research/unconditional-finite-price-kernel-2026-09-26.md ] || { echo "finite candidate price research note missing"; exit 1; }
    grep -Fq 'CertifiedEGraphEdge' Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda || { echo "e-graph certificate surface missing"; exit 1; }
    [ -f docs/research/theorem-improvement-completion-2026-09-26.md ] || { echo "theorem improvement research note missing"; exit 1; }
    [ -f .ci/discovery/theorem-improvement-completion-2026-09-26.mmd ] || { echo "theorem improvement graph missing"; exit 1; }

    grep -Fq 'UnconditionalAgdaEGraphAStarClosure' Exotic/ERL/FullCoupled/RepositorySemanticEGraphClosure.agda || { echo "repository-wide e-graph closure missing"; exit 1; }
    for module in canonicalLearnerMonolith theoremsMonolith eGraphSemanticTransport fourLawClosureWitnesses fourLawClosureImpossibility gruStatisticalInjectivity zpfStatisticalRepresentation tsallisStatisticalRepresentation repositorySemanticEGraphClosure
    do
      grep -Fq "$module" Exotic/ERL/FullCoupled/RepositorySemanticEGraphClosure.agda || { echo "Agda semantic index missing: $module"; exit 1; }
    done
    for file in CanonicalLearnerMonolith.agda TheoremsMonolith.agda EGraphSemanticTransport.agda FourLawClosureWitnesses.agda FourLawClosureImpossibility.agda GRUStatisticalInjectivity.agda CommonsComposition.agda GRUFractalInjectiveComposition.agda GRUFractalInjectiveCompositionCanonical.agda ZPFStatisticalRepresentation.agda TsallisStatisticalRepresentation.agda RepositorySemanticEGraphClosure.agda
    do
      [ -f "Exotic/ERL/FullCoupled/$file" ] || { echo "surviving Agda file missing from repository surface: $file"; exit 1; }
    done
    grep -Fq 'Complete surviving-Agda closure index' "$readme" || { echo "README missing complete Agda closure index"; exit 1; }
    law_count=$(awk -F': ' '/"semantic_law_count":/ {gsub(/[^0-9]/,"",$2); print $2; exit}' "$sync")
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
      printf '  "source_graph": "%s",\\n' "$graph"
      printf '  "theorem_source": "%s",\\n' "$theorem"
      printf '  "learner_source": "%s",\\n' "$learner"
      printf '  "semantic_law_count": %s,\\n' "$law_count"
      printf '  "record_count": %s,\\n' "$record_count"
      printf '  "top_level_declaration_count": %s,\\n' "$declaration_count"
      printf '  "economic_record_count": %s,\\n' "$economic_record_count"
      printf '  "economic_declaration_count": %s,\\n' "$economic_declaration_count"
      printf '  "counterexample_or_boundary_record_count": %s,\\n' "$counterexample_count"
      printf '  "composition_transport_record_count": %s,\\n' "$composition_count"
      printf '  "surface_authority": "TheoremsMonolith.agda",\\n'
      printf '  "dependency_authority": "theorem-monolith-egraph-sync.json",\\n'
      printf '  "frontier_policy": "PROVED | CONDITIONAL | FRONTIER | BLOCKED-BY-COUNTEREXAMPLE",\\n'
      printf '  "closed_core": ["CanonicalMARLLawCompositionTheorem", "CanonicalGRUF4NormWatkinsPrefixCompositionTheorem", "CanonicalNormPairQuotientFactorTransitionTheorem", "CanonicalF4GlobalOptimizerStabilityTheorem", "CanonicalF4NormPairUnconditionalFactorStabilityTheorem", "f4-unit-forcing-linear-growth", "f4-unit-forcing-no-upper-bound"],\\n'
      printf '  "composition_frontier": ["CanonicalLearnerHodgeMaxwellCompositionTheorem requires explicit Hodge representation and learner-step conjugacy witnesses"],\\n'
      printf '  "economic_boundary": ["learner factor stability does not entail convergence", "learner factor stability does not entail a fixed point", "learner factor stability does not entail market clearing", "learner factor stability does not entail supporting prices", "learner factor stability does not entail Walrasian existence"],\\n'
      printf '  "production_topology": "competitive production -> feasible plans -> profit-maximizing production -> demand -> aggregate resource balance -> market clearing -> derived/supporting price -> generalized Walrasian equilibrium",\\n'
      printf '  "counterexample_policy": "the singleton empty-equilibrium model blocks promotion of unconditional generalized-Walrasian existence",\\n'
      printf '  "automation": "one unattended Mercury discovery pass followed by deterministic semantic projection; JSON is machine evidence and Mermaid is the human topology view"\\n'
      printf '%s\\n' '}'
    } > .ci/discovery/economic-closure-graph.json

    grep -Fq '"surface_authority": "TheoremsMonolith.agda"' .ci/discovery/economic-closure-graph.json
    grep -Fq '"frontier_policy": "PROVED | CONDITIONAL | FRONTIER | BLOCKED-BY-COUNTEREXAMPLE"' .ci/discovery/economic-closure-graph.json
    echo "economic-closure-graph=pass"
    echo "economic-record-count=$economic_record_count"
    echo "economic-declaration-count=$economic_declaration_count"
    echo "counterexample-boundary-record-count=$counterexample_count"
    echo "composition-transport-record-count=$composition_count"
    '',
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
    local_theorem="Exotic/ERL/FullCoupled/TheoremsMonolith.agda"

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
      printf '  "local_mega_equilibrium_target": "GeneralizedWalrasianExistence",\n'
      printf '  "local_composition_target": "CanonicalLearnerHodgeMaxwellCompositionTheorem",\n'
      printf '  "local_mega_edge": "MegaGeneralizedWalrasianEquilibrium",\n'
      printf '  "adapter_present": %s,\n' "$adapter_present"
      printf '  "composition_path": ["Econlib::Economy.exists_equilibrium", "Actions::MegaGeneralizedWalrasianEquilibrium", "Actions::CanonicalLearnerHodgeMaxwellCompositionTheorem"],\n'
      printf '  "graph_status": "composition-ready; explicit cross-language adapter still required"\n'
      printf '%s\n' '}'
    } > .ci/discovery/econlib-crossrepo-sync.json

    grep -Fq '"upstream_static_existence": "Economy.exists_equilibrium"' .ci/discovery/econlib-crossrepo-sync.json
    grep -Fq '"local_composition_target": "CanonicalLearnerHodgeMaxwellCompositionTheorem"' .ci/discovery/econlib-crossrepo-sync.json
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
    local_theorem="Exotic/ERL/FullCoupled/TheoremsMonolith.agda"

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
    grep -Riq 'POMDP|partially observable' "$root/Econlib" && pomdp_named=true || true

    mkdir -p .ci/discovery
    {
      printf '%s\n' '{'
      printf '  "econlib_repo": "danlyng/Econlib",\n'
      printf '  "econlib_commit": "%s",\n' "$econlib_rev"
      printf '  "benchmark_regular_assumption": "Econlib::RegularEconomy",\n'
      printf '  "benchmark_static_existence": "Econlib::Economy.exists_equilibrium",\n'
      printf '  "non_iid_transition": "arbitrary Markov/kernel transition",\n'
      printf '  "stationary_law_node": "FiniteMarkovChain.exists_stationary",\n'
      printf '  "stationary_law_convergence_node": "FiniteMarkovChain.geometric_convergence_to",\n'
      printf '  "stationary_law_convergence_condition": "strictly positive transition probabilities",\n'
      printf '  "stationary_equilibrium_node": "MarkovExchangeEconomy.StationaryWalrasianEquilibrium",\n'
      printf '  "local_mega_edge": "MegaGeneralizedWalrasianEquilibrium",\n'
      printf '  "local_composition": "CanonicalLearnerHodgeMaxwellCompositionTheorem",\n'
      printf '  "partial_observation_nodes": ["BehavioralStrategy", "BeliefSystem", "SequentialEquilibrium"],\n'
      printf '  "pomdp_named_in_econlib": %s,\n' "$pomdp_named"
      printf '  "composition_path": ["Econlib::RegularEconomy", "Econlib::Economy.exists_equilibrium", "Actions::MegaGeneralizedWalrasianEquilibrium", "Actions::CanonicalLearnerHodgeMaxwellCompositionTheorem"],\n'
      printf '  "pomdp_bridge_status": "local POMDP belief-policy closure remains explicit; no filtering or optimality is inferred"\n'
      printf '%s\n' '}'
    } > .ci/discovery/econlib-equilibrium-graph.json

    grep -Fq '"regularity_assumption": "RegularEconomy"' .ci/discovery/econlib-equilibrium-graph.json
    grep -Fq '"non_iid_transition": "arbitrary Markov/kernel transition"' .ci/discovery/econlib-equilibrium-graph.json
    grep -Fq '"pomdp_bridge_status": "frontier:' .ci/discovery/econlib-equilibrium-graph.json
    echo "econlib-equilibrium-search=pass"
    echo "econlib-commit=$econlib_rev"
    echo "pomdp-named-in-upstream=$pomdp_named"
    '',
  StrictExistenceImpossibility = ''
    set -euo pipefail
    (cd .ci/discovery && mmc --make strict_existence_impossibility_graph && ./strict_existence_impossibility_graph)
    report=.ci/discovery/strict-existence-impossibility-graph.json
    grep -Fq '"rule": "STRICT_EXISTENCE_OR_IMPOSSIBILITY_ONLY"' "$report" || { echo "strict rule missing"; exit 1; }
    grep -Fq '"orange_statuses_allowed": false' "$report" || { echo "orange status enabled"; exit 1; }
    grep -Fq '"terminal_statuses": ["EXISTENCE","IMPOSSIBILITY"]' "$report" || { echo "non-strict terminal status present"; exit 1; }
    ! grep -Eiq 'frontier|unknown|vague|adapter needed|unresolved|pending' "$report" || { echo "vague status present"; exit 1; }
    grep -Fq 'strict-existence-impossibility-graph=pass' "$report"
    '',
  StationaryCycleImpossibility = ''
    set -euo pipefail
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT
    git clone --quiet --depth 1 https://github.com/danlyng/Econlib.git "$tmp/Econlib"

    theorem=Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    ergodic="$tmp/Econlib/Econlib/Probability/Markov/Ergodic.lean"

    grep -Fq 'canonicalNoNontrivialFiniteCycle-theorem' "$theorem"
    grep -Fq 'canonicalNoFiniteStepConvergenceToFixedPoint' "$theorem"
    grep -Fq 'isomorphismNoFiniteCycleTransport' "$theorem"
    grep -Fq 'exists_stationary' "$ergodic"
    grep -Fq 'theorem geometric_convergence_to' "$ergodic"
    grep -Fq '0 < P.transition' "$ergodic"

    mkdir -p .ci/discovery
    cat > .ci/discovery/stationary-cycle-impossibility-graph.json <<'JSON'
{
  "rule": "FINITE_DETERMINISTIC_CYCLE_HAS_STATIONARY_WITNESS_BUT_IS_EXCLUDED",
  "terminal_status": "IMPOSSIBILITY",
  "requires_exact_finite_deterministic_projection": true,
  "stationary_distribution_witness": {
    "type": "uniform_cycle_measure",
    "statement": "For a deterministic cycle of length m>0, the uniform probability law on the cycle is stationary for the induced deterministic Markov kernel.",
    "use": "witness_only"
  },
  "upstream_stationary_law": {
    "theorem": "Econlib::FiniteMarkovChain.exists_stationary",
    "role": "independent finite-state existence fact; it does not imply that a cycle exists"
  },
  "convergence_guard": {
    "theorem": "Econlib::FiniteMarkovChain.geometric_convergence_to",
    "condition": "strictly positive transition probabilities",
    "role": "separate conditional convergence result; not used to claim convergence of an arbitrary deterministic cycle"
  },
  "nodes": [
    "Agda::finiteOrbit-collision",
    "deterministic finite recurrent cycle",
    "uniform cycle stationary law",
    "Econlib::FiniteMarkovChain.exists_stationary",
    "Econlib::FiniteMarkovChain.geometric_convergence_to",
    "Agda::canonicalNoNontrivialFiniteCycle-theorem",
    "Agda::canonicalNoFiniteStepConvergenceToFixedPoint"
  ],
  "edges": [
    ["finiteOrbit-collision", "eventual periodic orbit"],
    ["eventual periodic orbit", "deterministic finite recurrent cycle"],
    ["deterministic finite recurrent cycle", "uniform cycle stationary law"],
    ["Econlib::FiniteMarkovChain.exists_stationary", "stationary distribution", "independent existence witness"],
    ["Econlib::FiniteMarkovChain.geometric_convergence_to", "quantitative convergence", "requires strict positivity"],
    ["deterministic finite recurrent cycle", "canonicalNoNontrivialFiniteCycle-theorem", "contradiction"],
    ["period-1 recurrent cycle", "canonicalNoFiniteStepConvergenceToFixedPoint", "contradiction"]
  ],
  "logic_guard": "stationary-law existence is not itself an obstruction; the obstruction is the canonical no-cycle theorem",
  "isomorphism_transport_node": "Agda::isomorphismNoFiniteCycleTransport",
  "isomorphism_transport_role": "exact conjugacy preserves finite-cycle exclusion on the isomorphic state space",
  "status": "strict graph: no third terminal status"
}
JSON
    grep -Fq '"terminal_status": "IMPOSSIBILITY"' .ci/discovery/stationary-cycle-impossibility-graph.json
    grep -Fq '"stationary_distribution_witness": {' .ci/discovery/stationary-cycle-impossibility-graph.json
    grep -Fq '"type": "uniform_cycle_measure"' .ci/discovery/stationary-cycle-impossibility-graph.json
    grep -Fq '"logic_guard": "stationary-law existence is not itself an obstruction; the obstruction is the canonical no-cycle theorem"' .ci/discovery/stationary-cycle-impossibility-graph.json
    grep -Fq '"requires_exact_finite_deterministic_projection": true' .ci/discovery/stationary-cycle-impossibility-graph.json
    grep -Fq '"status": "strict graph: no third terminal status"' .ci/discovery/stationary-cycle-impossibility-graph.json
    ! grep -Eiq 'frontier|unknown|vague|unresolved|pending' .ci/discovery/stationary-cycle-impossibility-graph.json
    echo "stationary-cycle-impossibility-graph=pass"
    '',
  IsomorphismTransport = ''
    set -euo pipefail
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    (cd .ci/discovery && mmc --make isomorphism_transport_graph && ./isomorphism_transport_graph)
    report=.ci/discovery/isomorphism-transport-graph.json
    grep -Fq '"rule": "ISOMORPHISM_TRANSPORT_CLOSURE"' "$report" || { echo "isomorphism transport rule missing"; exit 1; }
    grep -Fq '"orange_statuses_allowed": false' "$report" || { echo "orange status enabled"; exit 1; }
    grep -Fq 'Agda::isomorphismEqualityTransport' "$report" || { echo "equality transport kernel missing"; exit 1; }
    grep -Fq 'Agda::isomorphismDisequalityTransport' "$report" || { echo "disequality transport kernel missing"; exit 1; }
    ! grep -Eiq 'frontier|unknown|vague|unresolved|pending' "$report" || { echo "vague transport status present"; exit 1; }
    ''
,
  SemanticContract = ''
    set -euo pipefail
    theorem=Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    learner=Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    required='
    CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
    canonical-q-munchausen-l2-shared-negation-polarity-theorem
    canonicalWatkinsTarget-minimaxBellmanShapley-inclusion-class
    DirectProductFiniteAutomatonComposition
    canonical-recurrent-prefix-monoid-homomorphism
    canonicalF4-prefix-monoid-homomorphism
    canonicalNormPair-prefix-monoid-homomorphism
    canonicalGRUF4Norm-prefix-monoid-homomorphism
    canonicalFullStep-GRUF4Norm-prefix-bridge
    canonical-gruf4-norm-watkins-prefix-composition-theorem
    FreeMonoidActionHomomorphism
    freeMonoidActionHomomorphism-from-square
    canonicalCount-freeMonoidActionHomomorphism
    ExactNatObservationSimulation
    ContinuousLeftInverseTheorem
    canonicalRingStateInjective
    canonicalDenseNeighborhoodSeparation
    canonicalNoNontrivialFiniteCycle-theorem
    isomorphismIterateConjugacy
    isomorphismToInjective
    isomorphismEqualityTransport
    isomorphismDisequalityTransport
    isomorphismNoFiniteCycleTransport
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
    canonical-a-star-cost-guidance-theorem
    canonical-linear-haar-sparsemax-attention-composition-theorem
    canonical-full-state-haar-sparsemax-invariant-composition-theorem
    CanonicalLearnerReplacementClosureTheorem
    canonical-learner-replacement-closure-theorem
    RecurrentScanConjugacyTheorem
    recurrentPrefix-scan-lifts-conjugacy
    canonical-recurrent-scan-conjugacy-theorem
    CanonicalFullLearnerConnectedScanConjugacyTheorem
    canonical-full-learner-connected-scan-conjugacy-theorem
    canonicalExactCompositionTuringCompletenessContract-impossible
    canonical-haar-sparsemax-full-state-closure-theorem
    canonical-finite-factor-recurrence-without-state-recurrence
    canonical-finite-observation-information-boundary-theorem
    canonical-bounded-factor-lift-theorem
    CanonicalFiniteCycleExclusionIsomorphismTheorem
    canonical-finite-cycle-exclusion-isomorphism-theorem
    CanonicalOperatorCompositionTheorem
    canonical-operator-composition-theorem
    CanonicalPureNonOrangeBypassCompletionTheorem
    canonical-pure-non-orange-bypass-completion-theorem
    StationaryLimitTheorem
    stationaryLimitTheorem-is-stationary
    TopologicalConvergenceWitness
    topologicalConvergenceFixedPoint
    FixedPointExistenceFromConvergence
    fixedPoint-from-convergence
    isomorphismFixedPointTransport
    isomorphismIterateFixedPointTransport
    TransportedFixedPointExistence
    transportedFixedPointExistence-witness
    EquilibriumFixedPointClosure
    equilibrium-from-fixed-point
    economicEquilibriumExistenceFromConvergentFixedPoint
    CanonicalStationarySubcompositionTheorem
    CanonicalPersistentExcitationRequirementTheorem
    canonical-persistent-excitation-requirement-theorem
    ExactContractComputabilityBoundaryTheorem
    exact-contract-computability-boundary-theorem
    ExactFunctionIsomorphismTransportTheorem
    ExactRecurrentFunctionTranslationTheorem
    MegaWalrasianGlobalSquareConjugacy
    megaWalrasianGlobalSquare-injective
    MegaParetoImprovement
    megaParetoOptimal
    MegaFirstWelfareTheoremConditions
    megaFirstWelfareTheorem
    MegaSecondWelfareTheoremConditions
    megaSecondWelfareTheorem
    MegaSecondWelfareTheoremBoundaryCounterexample
    megaSecondWelfareTheorem-boundary-counterexample
    MegaNoStrictAffordableAlternativeBoundary
    megaNoStrictAffordableAlternative-is-demand-optimality
    MegaParetoEquilibriumConditionality
    MegaWalrasianEquilibriumWelfareAdapter
    MegaInterdependentGRUMegaWalrasianGlobalSquareCompositionCompleteness
    MegaGeneralizedWalrasianEquilibrium
    MegaGeneralizedWalrasianEquilibrium
    POMDPWalrasianData
    POMDPWalrasianEquilibrium
    POMDPWalrasianTransport
    POMDPBeliefPolicyFactorization
    POMDPWalrasianBeliefEquilibriumClosure
    CanonicalLearnerHodgeMaxwellCompositionTheorem
    NLabMaxwellSemanticClosure
    NLabMaxwellFourLawSemanticallyClosed
    nLabMaxwellEulerLagrangeShell-equivalence
    nLabMaxwellFourLawOneStepClosed
    nLabMaxwellIterateConjugacyClosed
    POMDPExactTransport
    CanonicalGlobalTokenEncodingConjugacyTheorem
    CanonicalGlobalTokenLMCompositionTheorem
    CanonicalLearnerHodgeMaxwellCompositionTheorem
    CanonicalF4NormPairGRUGlobalConjugacyInjectivityTheorem
    CanonicalLearnerHodgeMaxwellCompositionTheorem
    CanonicalLearnerHodgeMaxwellCompositionTheorem
    CanonicalLearnerHodgeMaxwellCompositionTheorem
    CanonicalLearnerHodgeMaxwellCompositionTheorem
    CanonicalExactRNNLMTheorem
    canonical-exact-turing-boundary-mixture-theorem
    bairdSevenStar
    majority3ShapleyEquilibriumWitness
    '
    while IFS= read -r symbol; do
      [ -z "$symbol" ] || grep -Fq "$symbol" "$theorem" || { echo "missing theorem symbol: $symbol"; exit 1; }
    done <<< "$required"
    [ ! -f .ci/discovery/learner_semantic_manifest.m ] || { echo "generated semantic lookup table present"; exit 1; }
    [ ! -f .ci/discovery/learner-semantic-laws.tsv ] || { echo "generated semantic law artifact present"; exit 1; }
    grep -Eiq 'walsh|rope|target-network|target_network|target network|normalization|regularization' "$learner" && { echo "forbidden semantic term present"; exit 1; } || true
    grep -Fq 'open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C' "$theorem" || { echo "non-canonical theorem source"; exit 1; }
    '',
  Surface = ''
    set -euo pipefail
    count=$(git ls-files '*Monolith.agda' | wc -l)
    [ "$count" -eq 2 ] || { echo "expected exactly two Agda monoliths, found $count"; exit 1; }
    [ -f .ci/actions_ci.dhall ] || { echo "missing Dhall orchestrator"; exit 1; }
    ! git ls-files '*.roc' | grep -q . || { echo "Roc source remains"; exit 1; }
    forbidden='\.sh$|\.bash$|\.zsh$|\.fish$|\.cmd$|\.bat$|\.ps1$|\.command$|\.py$|\.java$|\.kt$|\.scala$|\.groovy$|\.clj$|\.cljs$|\.js$|\.mjs$|\.cjs$|\.ts$|\.tsx$|\.elm$|\.purs$|\.hs$|\.lhs$|\.cabal$|\.lua$|\.nim$|\.nims$|\.rocx$|\.ml$|\.mli$|\.sml$|\.c$|\.h$|\.cc$|\.cpp$|\.cxx$|\.hpp$|\.hxx$|\.cs$|\.fs$|\.fsx$|\.vb$|\.csproj$|\.fsproj$|\.vbproj$|\.sln$|\.html$|\.htm$|\.css$|\.tex$|\.ltx$|\.sty$|\.cls$|\.bib$|\.scm$|\.scheme$|\.ss$|\.rkt$'
    ! git ls-files | grep -E "$forbidden" || { echo "forbidden source suffix present"; exit 1; }
    retired='guix|guile|scheme|evolutionary-search|evolutionary algorithm|sparsemax2pair|fixedtemperaturesparsemax|actionscore|policyleftweight|tsts|gresher'
    ! git ls-files -z | xargs -0 grep -Eil "$retired" 2>/dev/null | grep -q . || { echo "retired term present"; exit 1; }
    '',
  Versions = ''
    set -euo pipefail
    "$AGDA_COMMAND" --version
    mmc --version
    dhall --version
    '',
  AutoMerge = ''
    set -euo pipefail
    : "${GH_TOKEN:?GH_TOKEN is required}"
    : "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is required}"
    : "${PR_NUMBER:?PR_NUMBER is required}"
    gh pr merge "$PR_NUMBER" --repo "$GITHUB_REPOSITORY" --auto --rebase
    '',
  All = ''
    set -euo pipefail
    "$AGDA_COMMAND" --version
    mmc --version
    dhall --version
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CanonicalLearnerMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TheoremsMonolith.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/EGraphSemanticTransport.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/FourLawClosureWitnesses.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/FourLawClosureImpossibility.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUStatisticalInjectivity.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/CommonsComposition.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalInjectiveComposition.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalInjectiveCompositionCanonical.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/GRUFractalDomainAdapters.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/ZPFStatisticalRepresentation.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/TsallisStatisticalRepresentation.agda
    "$AGDA_COMMAND" --safe -l standard-library -i . Exotic/ERL/FullCoupled/RepositorySemanticEGraphClosure.agda
    (cd .ci && mmc --make check_forbidden_theorems && ./check_forbidden_theorems)
    (cd .ci/discovery && mmc --make theorem_registry_reconcile && ./theorem_registry_reconcile --check)
    (cd .ci/discovery && mmc --make theorem_monolith_egraph_sync && ./theorem_monolith_egraph_sync)
    (cd .ci/discovery && mmc --make symbolic_egraph_test && ./symbolic_egraph_test)
    (cd .ci/discovery && mmc --make interpolated_theorem_egraph_test && ./interpolated_theorem_egraph_test)
    ''
}
