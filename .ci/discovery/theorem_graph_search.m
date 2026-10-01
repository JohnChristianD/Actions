:- module theorem_graph_search.

:- interface.

:- import_module bool.
:- import_module int.
:- import_module list.
:- import_module string.
:- import_module learner_semantic_extractor.

:- pred search_emergent_compositions(
    list(semantic_law)::in,
    list(list(string))::out) is det.

:- pred search_emergent_composition(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred search_all_composite_law_plans(
    list(semantic_law)::in,
    list(list(string))::out) is det.

:- pred search_endogenous_composite_plans(
    list(semantic_law)::in,
    list(list(string))::out) is det.

:- pred graph_search_completion(
    list(semantic_law)::in,
    list(list(string))::out,
    list(list(string))::out) is semidet.




:- pred graph_stationary_limit_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_stationary_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.




:- pred graph_connected_jensen_minimax_regret_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred all_scores_non_decreasing(
    list(semantic_law)::in,
    list(list(string))::in) is semidet.

:- pred all_generated_plans_valid(
    list(semantic_law)::in,
    list(list(string))::in) is semidet.

:- pred search_emergent_compositions_from_seed_ids(
    list(semantic_law)::in,
    list(string)::in,
    list(list(string))::out) is det.

:- pred graph_astar_haskell_monad_surface_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_canonical_f4_integer_layernorm_stability_boundary_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_astar_plan_monoid_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_integer_layernorm_egraph_astar_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_integer_layernorm_configuration_stability_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_integer_layernorm_epsilon_ray_growth_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_canonical_integer_layernorm_egraph_astar_infinite_horizon_stability_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_review_frontier_plans(
    list(semantic_law)::in,
    list(list(string))::out) is det.

:- pred graph_dominance_edges(
    list(semantic_law)::in,
    list(string)::out) is det.

:- pred graph_dominated_public_theorems(
    list(semantic_law)::in,
    list(string)::out) is det.

:- func graph_pruned_public_theorem_names = list(string).

:- pred graph_canonical_integer_layernorm_stability_growth_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_canonical_integer_gru_global_conjugate_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_gru_fractal_limit_convergence_adapter_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_canonical_integer_gru_fractal_limit_composition_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_gru_injective_tail_stability_convergence_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_finite_mixed_nash_brouwer_egraph_astar_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_finite_mixed_nash_egraph_astar_convergence_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_finite_mixed_nash_cycle_transport_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

:- pred graph_finite_mixed_nash_gru_tail_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.


:- implementation.


graph_gru_fractal_limit_convergence_adapter_plan(Laws, Plan) :-
    search_named_required_plan(
        "GRUFractalLimitConvergenceWitness",
        Laws,
        Plan).


graph_canonical_integer_gru_fractal_limit_composition_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalIntegerGRUFractalLimitCompositionTheorem",
        Laws,
        Plan).

graph_gru_injective_tail_stability_convergence_plan(Laws, Plan) :-
    search_named_required_plan(
        "GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem",
        Laws,
        Plan).

graph_finite_mixed_nash_brouwer_egraph_astar_plan(Laws, Plan) :-
    search_named_required_plan(
        "finiteMixedNash-brouwer-egraph-astar-proof",
        Laws,
        Plan).

graph_finite_mixed_nash_egraph_astar_convergence_plan(Laws, Plan) :-
    search_named_required_plan(
        "finiteMixedNash-egraph-astar-convergence",
        Laws,
        Plan).

graph_finite_mixed_nash_cycle_transport_plan(Laws, Plan) :-
    search_named_required_plan(
        "finiteMixedNash-cycle-transport",
        Laws,
        Plan).

graph_finite_mixed_nash_gru_tail_plan(Laws, Plan) :-
    search_named_required_plan(
        "finiteMixedNash-from-GRU-tail",
        Laws,
        Plan).

graph_stationary_limit_plan(Laws, Plan) :-
    search_named_required_plan(
        "StationaryLimitTheorem",
        Laws,
        Plan).

graph_stationary_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalStationarySubcompositionTheorem",
        Laws,
        Plan).

graph_connected_jensen_minimax_regret_plan(Laws, Plan) :-
    graph_connected_f4_frank_wolfe_rounding_bias_regret_plan(Laws, Plan).

:- pred graph_connected_custom_optimizer_rounding_bias_regret_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

graph_connected_custom_optimizer_rounding_bias_regret_plan(Laws, Plan) :-
    graph_connected_f4_frank_wolfe_rounding_bias_regret_plan(Laws, Plan).

:- pred graph_connected_f4_frank_wolfe_rounding_bias_regret_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

graph_connected_f4_frank_wolfe_rounding_bias_regret_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalF4GlobalOptimizerStabilityTheorem",
        Laws,
        Plan).

all_generated_plans_valid(Laws, Plans) :-
    all_valid_plans(Plans, Laws, yes).

:- type graph_node
    ---> graph_node(
        plan :: list(string)
    ).

:- pred law_for_id(
    string::in, list(semantic_law)::in, semantic_law::out) is semidet.
law_for_id(_, [], _) :-
    fail.
law_for_id(Id, [Law | Laws], Result) :-
    (
        if law_id(Law) = Id then
            Result = Law
        else
            law_for_id(Id, Laws, Result)
    ).

:- pred seed_node(semantic_law::in, graph_node::out) is semidet.
seed_node(Law, Node) :-
    not is_reflexive(Law),
    not is_record_field(Law),
    Node = graph_node([law_id(Law)]).

:- pred seed_nodes(
    list(semantic_law)::in,
    list(graph_node)::out) is det.
seed_nodes([], []).
seed_nodes([Law | Laws], Nodes) :-
    seed_nodes(Laws, Tail),
    (
        if seed_node(Law, Node) then
            Nodes = [Node | Tail]
        else
            Nodes = Tail
    ).

:- pred expand_node(
    graph_node::in,
    list(semantic_law)::in,
    list(graph_node)::out) is det.
expand_node(graph_node([]), _, []).
expand_node(graph_node([TerminalId | Rest]), Laws, Children) :-
    Plan0 = [TerminalId | Rest],
    (
        if law_for_id(TerminalId, Laws, TerminalLaw) then
            expand_dependencies(
                law_dependencies(TerminalLaw),
                Plan0,
                [],
                Children)
        else
            Children = []
    ).

:- pred expand_dependencies(
    list(string)::in,
    list(string)::in,
    list(graph_node)::in,
    list(graph_node)::out) is det.
expand_dependencies([], _, Acc, Children) :-
    list.reverse(Acc, Children).
expand_dependencies([Dependency | Dependencies], Plan, Acc0, Children) :-
    (
        if list.member(Dependency, Plan) then
            expand_dependencies(Dependencies, Plan, Acc0, Children)
        else
            expand_dependencies(
                Dependencies,
                [Dependency | Plan],
                [graph_node([Dependency | Plan]) | Acc0],
                Children)
    ).

:- pred maximal_dependency_chain(
    graph_node::in,
    list(semantic_law)::in) is semidet.
maximal_dependency_chain(Node, Laws) :-
    expand_node(Node, Laws, []).

:- func node_score(list(semantic_law), graph_node) = int.
node_score(Laws, graph_node(Plan)) =
    length(Plan) + node_heuristic(Laws, Plan).

:- func node_heuristic(list(semantic_law), list(string)) = int.
node_heuristic(_, []) = 0.
node_heuristic(Laws, [TerminalId | _]) =
    (
        if law_for_id(TerminalId, Laws, Law),
           law_dependencies(Law) = []
        then
            0
        else
            1
    ).

:- pred insert_astar(list(semantic_law)::in, graph_node::in, list(graph_node)::in, list(graph_node)::out) is det.
insert_astar(_, Node, [], [Node]).
insert_astar(Laws, Node, [Head | Tail], Result) :-
    (
        if node_score(Laws, Node) =< node_score(Laws, Head) then
            Result = [Node, Head | Tail]
        else
            insert_astar(Laws, Node, Tail, TailResult),
            Result = [Head | TailResult]
    ).

:- pred insert_astar_children(
    list(semantic_law)::in,
    list(graph_node)::in,
    list(graph_node)::in,
    list(graph_node)::out) is det.
insert_astar_children(_, [], Frontier, Frontier).
insert_astar_children(Laws, [Node | Nodes], Frontier0, Frontier) :-
    insert_astar(Laws, Node, Frontier0, Frontier1),
    insert_astar_children(Laws, Nodes, Frontier1, Frontier).

:- pred astar_collect(
    list(semantic_law)::in,
    list(graph_node)::in,
    list(list(string))::in,
    list(list(string))::out) is det.
astar_collect(_, [], Results, Results).
astar_collect(Laws, [Node | Frontier], Results0, Results) :-
    (
        if maximal_dependency_chain(Node, Laws) then
            astar_collect(
                Laws, Frontier,
                [Node ^ plan | Results0], Results)
        else
            expand_node(Node, Laws, Children),
            insert_astar_children(Laws, Children, Frontier, Frontier1),
            astar_collect(
                Laws, Frontier1, Results0, Results)
    ).


:- pred all_unique(list(string)::in) is semidet.
all_unique([]).
all_unique([X | Xs]) :-
    not list.member(X, Xs),
    all_unique(Xs).

:- pred valid_plan(
    list(string)::in, list(semantic_law)::in) is semidet.
valid_plan(Plan, Laws) :-
    Plan = [TerminalId | _],
    all_unique(Plan),
    valid_chain(Plan, Laws),
    law_for_id(TerminalId, Laws, _).

:- pred valid_chain(list(string)::in, list(semantic_law)::in) is semidet.
valid_chain([_], _).
valid_chain([Child, Parent | Rest], Laws) :-
    law_for_id(Parent, Laws, ParentLaw),
    list.member(Child, law_dependencies(ParentLaw)),
    valid_chain([Parent | Rest], Laws).

:- pred plan_score(
    list(semantic_law)::in,
    list(string)::in,
    int::out) is det.
plan_score(Laws, Plan, Score) :-
    Score = node_score(Laws, graph_node(Plan)).

all_scores_non_decreasing(_, []).
all_scores_non_decreasing(_, [_]).
all_scores_non_decreasing(Laws, [First, Second | Rest]) :-
    plan_score(Laws, First, FirstScore),
    plan_score(Laws, Second, SecondScore),
    FirstScore =< SecondScore,
    all_scores_non_decreasing(Laws, [Second | Rest]).

:- pred all_valid_plans(
    list(list(string))::in, list(semantic_law)::in, bool::out) is det.
all_valid_plans([], _, yes).
all_valid_plans([Plan | Plans], Laws, Valid) :-
    (
        if valid_plan(Plan, Laws) then
            all_valid_plans(Plans, Laws, Valid)
        else
            Valid = no
    ).


:- pred law_for_name(
    string::in, list(semantic_law)::in, semantic_law::out) is semidet.
law_for_name(_, [], _) :-
    fail.
law_for_name(Name, [Law | Laws], Result) :-
    (
        if law_name(Law) = Name then
            Result = Law
        else
            law_for_name(Name, Laws, Result)
    ).

:- pred search_named_required_plan(
    string::in, list(semantic_law)::in, list(string)::out) is semidet.
search_named_required_plan(Name, Laws, Plan) :-
    law_for_name(Name, Laws, Law),
    seed_node(Law, Seed),
    astar_collect(Laws, [Seed], [], Results),
    first_plan(Results, Plan).

:- func normalized_signature(string) = string.
normalized_signature(Signature) =
    string.join_list(" ", string.words(Signature)).

:- pred record_field_dominates(
    semantic_law::in,
    list(semantic_law)::in,
    string::out,
    string::out) is semidet.
record_field_dominates(Theorem, Laws, Container, FieldName) :-
    not is_record_field(Theorem),
    not is_reflexive(Theorem),
    TheoremSignature = normalized_signature(law_signature(Theorem)),
    list.member(Field, Laws),
    is_record_field(Field),
    FieldSignature = normalized_signature(law_signature(Field)),
    FieldSignature = TheoremSignature,
    Container = law_container(Field),
    Container \= "",
    law_for_name(Container, Laws, _),
    FieldName = law_name(Field).

:- pred dominance_edges_for_law(
    semantic_law::in,
    list(semantic_law)::in,
    list(string)::in,
    list(string)::out) is det.
dominance_edges_for_law(Theorem, Laws, Acc0, Acc) :-
    dominance_edges_for_law_2(Theorem, Laws, Acc0, Acc).

:- pred dominance_edges_for_law_2(
    semantic_law::in,
    list(semantic_law)::in,
    list(string)::in,
    list(string)::out) is det.
dominance_edges_for_law_2(_, [], Acc, Acc).
dominance_edges_for_law_2(Theorem, [Field | Fields], Acc0, Acc) :-
    (
        if record_field_dominates(
            Theorem, [Field | Fields], Container, FieldName)
        then
            Edge = string.join_list(
                "",
                [Container, " -> ", law_name(Theorem),
                 " [field ", FieldName, "]"]),
            (
                if list.member(Edge, Acc0) then
                    Acc1 = Acc0
                else
                    Acc1 = [Edge | Acc0]
            )
        else
            Acc1 = Acc0
    ),
    dominance_edges_for_law_2(Theorem, Fields, Acc1, Acc).

graph_dominance_edges(Laws, Edges) :-
    graph_dominance_edges_2(Laws, Laws, [], Reversed),
    list.reverse(Reversed, Edges).

:- pred graph_dominance_edges_2(
    list(semantic_law)::in,
    list(semantic_law)::in,
    list(string)::in,
    list(string)::out) is det.
graph_dominance_edges_2([], _, Acc, Acc).
graph_dominance_edges_2([Law | Laws], All, Acc0, Acc) :-
    dominance_edges_for_law(Law, All, Acc0, Acc1),
    graph_dominance_edges_2(Laws, All, Acc1, Acc).

graph_dominated_public_theorems(Laws, Names) :-
    graph_dominated_public_theorems_2(Laws, Laws, [], Reversed),
    list.reverse(Reversed, Names).

:- pred graph_dominated_public_theorems_2(
    list(semantic_law)::in,
    list(semantic_law)::in,
    list(string)::in,
    list(string)::out) is det.
graph_dominated_public_theorems_2([], _, Acc, Acc).
graph_dominated_public_theorems_2([Law | Laws], All, Acc0, Acc) :-
    (
        if record_field_dominates(Law, All, _, _) then
            (
                if list.member(law_name(Law), Acc0) then
                    Acc1 = Acc0
                else
                    Acc1 = [law_name(Law) | Acc0]
            )
        else
            Acc1 = Acc0
    ),
    graph_dominated_public_theorems_2(Laws, All, Acc1, Acc).

:- func graph_pruned_public_theorem_names = list(string).
graph_pruned_public_theorem_names = [
    "integerLayerNorm-egraph-astar-eventual-semantic-closure",
    "integerLayerNorm-egraph-astar-infinite-stable-tail",
    "eGraphEconomicFixedPoint",
    "eGraphEconomicWalrasianEquilibrium",
    "eGraphEconomicComposition-injective"
].

:- pred every_pruned_name_is_dominated(
    list(string)::in,
    list(string)::in) is semidet.
every_pruned_name_is_dominated([], _).
every_pruned_name_is_dominated([Name | Names], Dominated) :-
    list.member(Name, Dominated),
    every_pruned_name_is_dominated(Names, Dominated).

:- pred graph_pruned_public_theorem_names_checked(
    list(semantic_law)::in,
    list(string)::out) is det.
graph_pruned_public_theorem_names_checked(Laws, Names) :-
    graph_dominated_public_theorems(Laws, Dominated),
    (
        if every_pruned_name_is_dominated(
            graph_pruned_public_theorem_names,
            Dominated)
        then
            Names = graph_pruned_public_theorem_names
        else
            Names = []
    ).

:- pred search_composite_law_plans(
    list(semantic_law)::in,
    list(semantic_law)::out) is det.
search_composite_law_plans([], []).
search_composite_law_plans([Law | Laws], Result) :-
    search_composite_law_plans(Laws, Tail),
    (
        if is_composite(Law), not is_record_field(Law) then
            Result = [Law | Tail]
        else
            Result = Tail
    ).

search_all_composite_law_plans(Laws, Plans) :-
    search_composite_law_plans(Laws, CompositeLaws),
    search_composite_law_plans_to_plans(Laws, CompositeLaws, Plans).

:- pred search_endogenous_composite_laws(
    list(semantic_law)::in,
    list(semantic_law)::out) is det.
search_endogenous_composite_laws([], []).
search_endogenous_composite_laws([Law | Laws], Result) :-
    search_endogenous_composite_laws(Laws, Tail),
    (
        if is_composite(Law),
           string.sub_string_search(law_name(Law), "endogenous", _)
        then
            Result = [Law | Tail]
        else
            Result = Tail
    ).

search_endogenous_composite_plans(Laws, Plans) :-
    search_endogenous_composite_laws(Laws, CompositeLaws),
    search_composite_law_plans_to_plans(Laws, CompositeLaws, Plans).

:- pred search_composite_law_plans_to_plans(
    list(semantic_law)::in,
    list(semantic_law)::in,
    list(list(string))::out) is det.
search_composite_law_plans_to_plans(_, [], []).
search_composite_law_plans_to_plans(Laws, [Law | Rest], [Plan | Plans]) :-
    (
        if search_named_required_plan(law_name(Law), Laws, Plan0) then
            Plan = Plan0
        else
            Plan = [law_id(Law)]
    ),
    search_composite_law_plans_to_plans(Laws, Rest, Plans).

:- pred all_named_required_plans(
    list(string)::in,
    list(semantic_law)::in,
    list(list(string))::out) is semidet.
all_named_required_plans([], _, []).
all_named_required_plans([Name | Names], Laws, [Plan | Plans]) :-
    search_named_required_plan(Name, Laws, Plan),
    all_named_required_plans(Names, Laws, Plans).

:- func graph_required_theorems = list(string).
graph_required_theorems = [
    "CanonicalAQLoopTheorem",
    "CanonicalConnectedCompositionTheorem",
    "EqualityCompositionTheorem",
    "RecurrentAssociativeScanTheorem",
    "CommutingSquareTheorem",
    "RecurrentScanConjugacyTheorem",
    "CanonicalFullLearnerConnectedScanConjugacyTheorem",
    "S4PlusS5RecurrentScanTheorem",
    "MinimaxBellmanShapleyInclusionTheorem",
    "CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem",
    "CanonicalQMunchausenL2SharedNegationPolarityTheorem",
    "DiscreteExactUAPTheorem",
    "DiscreteExactUniversalUAP",
    "CanonicalExactCompositionTuringCompletenessContract",
    "ContinuousLeftInverseTheorem",
    "RingStateInjectivityTheorem",
    "DenseNeighborhoodSeparationTheorem",
    "CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem",
    "CanonicalPolymorphicSparsemaxCompositionTheorem",
    "OffPolicyFunctionApproximationStabilityBoundary",
    "CanonicalLearnerBairdSevenStarWitness",
    "canonicalLearnerBairdSevenStar",
    "GlobalConjugacyEquivalence",
    "ExactFunctionIsomorphismTransportTheorem",
    "ExactRecurrentFunctionTranslationTheorem",
    "CanonicalExactRNNLMTheorem",
    "CanonicalGlobalTokenLMCompositionTheorem",
    "CanonicalIntegerHaarScaledOrthogonalityTheorem",
    "GenericRingSolverNormalizationTheorem",
    "NatRingSolverNormalizationTheorem",
    "IntegerRingSolverNormalizationTheorem",
    "ListMonoidSolverNormalizationTheorem",
    "CanonicalAlgebraicTacticBackendTheorem",
    "CanonicalSafeTacticNormalizationTheorem",
    "CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem",
    "AStarPlanMonoidTheorem",
    "CanonicalTokenArbitraryLengthGenerationTheorem",
    "NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem",
    "CanonicalAStarCostGuidanceTheorem",
    "CanonicalEndogenousEGraphAStarTransportClosureTheorem",
    "CanonicalFiniteCycleExclusionIsomorphismTheorem",
    "CanonicalOperatorCompositionTheorem",
    "CanonicalF4GlobalOptimizerStabilityTheorem",
    "CanonicalPureNonOrangeBypassCompletionTheorem",
    "CanonicalPersistentExcitationRequirementTheorem",
    "ExactContractComputabilityBoundaryTheorem",
    "EfficientOperatorMonoidRepresentation",
    "ParallelPrefixComplexityCertificate",
    "LogarithmicScanSpanCertificate",
    "LogarithmicPrefixScanComplexityTheorem",
    "ConnectedContinuousHodgeMaxwellGRURepresentationTheorem",
    "StateIsomorphism",
    "RecurrentPrefixMonoidHomomorphism",
    "FreeMonoidActionHomomorphism",
    "PointwiseSandwich",
    "MinimaxBellmanShapleyOperator",
    "DiscreteLeftInverseWitness",
    "ExactTwoCounterConfiguration",
    "ExactTwoCounterMachine",
    "ExactReconstructionOnImage",
    "StationaryLimitTheorem",
    "GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem",
    "BrouwerMixedNashExistence",
    "nashEveryFiniteGameViaBrouwer",
    "brouwerMixedNashFixedPointBridge",
    "finiteMixedNash-brouwer-egraph-astar-proof",
    "finiteMixedNash-egraph-astar-convergence",
    "finiteMixedNash-egraph-astar-eventualStationarity",
    "finiteMixedNash-egraph-astar-proof",
    "finiteMixedNash-cycle-transport",
    "finiteMixedNash-from-GRU-tail",
    "finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof",
    "finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof-nash",
    "finiteMixedNash-brouwer-gru-egraph-astar-distribution-fixed",
    "canonicalFullLearner-no-finite-rank-stability",
    "CanonicalIntegerGRUFractalLimitCompositionTheorem",
    "HiddenSynergyNormPair",
    "rowL1OnesAbs",
    "onePathOneLayer",
    "CanonicalHardSparsityDegeneracyTheorem",
    "ActionWeights",
    "actionSupportCount",
    "actionWeightSum",
    "actionWeightSquareSum",
    "generalTsallis2Denominator",
    "generalTsallis2Numerator",
    "generalTsallis2NearSparsity",
    "generalTsallis2NearSparsity-zero",
    "generalTsallis2NearSparsity-definition",
    "fractionEquivalent",
    "tsallis2Near-oneHot",
    "generalSupportSparsity",
    "generalSupportSparsity-definition",
    "UniformSupportTsallisBoundary"
].

:- func graph_required_subcompositions = list(string).
graph_required_subcompositions = [
    "CanonicalStationarySubcompositionTheorem",
].

graph_search_completion(Laws, RequirementPlans, SubcompositionPlans) :-
    all_named_required_plans(graph_required_theorems, Laws, RequirementPlans),
    all_named_required_plans(graph_required_subcompositions, Laws, SubcompositionPlans).

search_emergent_compositions(Laws, Results) :-
    seed_nodes(Laws, Seeds),
    astar_collect(Laws, Seeds, [], Reversed),
    list.reverse(Reversed, CandidateResults),
    all_valid_plans(CandidateResults, Laws, Valid),
    (
        if Valid = yes then
            Results = CandidateResults
        else
            Results = []
    ).

:- pred first_plan(
    list(list(string))::in, list(string)::out) is semidet.
first_plan([], _) :-
    fail.
first_plan([Plan | _], Plan).

search_emergent_composition(Laws, Plan) :-
    seed_nodes(Laws, Seeds),
    astar_collect(Laws, Seeds, [], Results),
    first_plan(Results, Plan).

:- pred seed_nodes_by_ids(
    list(string)::in,
    list(semantic_law)::in,
    list(graph_node)::out) is det.
seed_nodes_by_ids([], _, []).
seed_nodes_by_ids([Id | Ids], Laws, Nodes) :-
    seed_nodes_by_ids(Ids, Laws, Tail),
    (
        if law_for_id(Id, Laws, Law), seed_node(Law, Node) then
            Nodes = [Node | Tail]
        else
            Nodes = Tail
    ).

search_emergent_compositions_from_seed_ids(Laws, SeedIds, Results) :-
    seed_nodes_by_ids(SeedIds, Laws, Seeds),
    astar_collect(Laws, Seeds, [], Reversed),
    list.reverse(Reversed, CandidateResults),
    all_valid_plans(CandidateResults, Laws, Valid),
    (
        if Valid = yes then
            Results = CandidateResults
        else
            Results = []
    ).


graph_astar_haskell_monad_surface_plan(Laws, Plan) :-
    search_named_required_plan(
        "AStarHaskellMonadSurface",
        Laws,
        Plan).

graph_canonical_f4_integer_layernorm_stability_boundary_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalF4IntegerLayerNormStabilityBoundaryTheorem",
        Laws,
        Plan).

graph_astar_plan_monoid_plan(Laws, Plan) :-
    search_named_required_plan(
        "AStarPlanMonoidTheorem",
        Laws,
        Plan).

graph_integer_layernorm_egraph_astar_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalIntegerLayerNormEGraphAStarTheorem",
        Laws,
        Plan).

graph_integer_layernorm_configuration_stability_plan(Laws, Plan) :-
    search_named_required_plan(
        "IntegerLayerNormConfigurationStabilityTheorem",
        Laws,
        Plan).

graph_integer_layernorm_epsilon_ray_growth_plan(Laws, Plan) :-
    search_named_required_plan(
        "IntegerLayerNormEpsilonRayGrowthTheorem",
        Laws,
        Plan).

graph_canonical_integer_layernorm_egraph_astar_infinite_horizon_stability_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem",
        Laws,
        Plan).

graph_generic_ring_solver_plan(Laws, Plan) :-
    search_named_required_plan(
        "GenericRingSolverNormalizationTheorem",
        Laws,
        Plan).

graph_nat_ring_solver_plan(Laws, Plan) :-
    search_named_required_plan(
        "NatRingSolverNormalizationTheorem",
        Laws,
        Plan).

graph_integer_ring_solver_plan(Laws, Plan) :-
    search_named_required_plan(
        "IntegerRingSolverNormalizationTheorem",
        Laws,
        Plan).

graph_list_monoid_solver_plan(Laws, Plan) :-
    search_named_required_plan(
        "ListMonoidSolverNormalizationTheorem",
        Laws,
        Plan).

graph_canonical_algebraic_tactic_backend_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalAlgebraicTacticBackendTheorem",
        Laws,
        Plan).

graph_canonical_safe_tactic_normalization_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalSafeTacticNormalizationTheorem",
        Laws,
        Plan).

:- func graph_review_frontier_names = list(string).
graph_review_frontier_names = [
    "CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem",
    "AStarPlanMonoidTheorem",
    "CanonicalTokenArbitraryLengthGenerationTheorem",
    "NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem",
    "GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem",
    "finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof"
].

graph_review_frontier_plans(Laws, Plans) :-
    search_named_plans(
        Laws,
        graph_review_frontier_names,
        Plans).

:- pred search_named_plans(
    list(semantic_law)::in,
    list(string)::in,
    list(list(string))::out) is det.
search_named_plans(_, [], []).
search_named_plans(Laws, [Name | Names], Plans) :-
    search_named_plans(Laws, Names, Tail),
    (
        if search_named_required_plan(Name, Laws, Plan) then
            Plans = [Plan | Tail]
        else
            Plans = Tail
    ).

graph_canonical_integer_layernorm_stability_growth_plan(Laws, Plan) :-
    search_named_required_plan(
        "CanonicalIntegerLayerNormStabilityGrowthTheorem",
        Laws,
        Plan).



:- func graph_unconditional_target_edges = list(string).
graph_unconditional_target_edges = [
    "EconomicStructure -> demand + competitive supply",
    "demand + competitive supply -> aggregate balance + market clearing",
    "aggregate balance + market clearing -> economic update operator",
    "economic update operator -> TopologicalConvergenceWitness [FRONTIER]",
    "TopologicalConvergenceWitness -> FixedPointExistenceFromConvergence",
    "fixed-point witness -> GeneralizedWalrasianFixedPointClosure [FRONTIER]",
    "GeneralizedWalrasianExistence -> unconditional existence target"
].
:- pred graph_canonical_integer_gru_global_conjugate_plan(
    list(semantic_law)::in,
    list(string)::out) is semidet.

graph_canonical_integer_gru_global_conjugate_plan(Laws, Plan) :-
    search_named_required_plan(
        "canonical-integer-gru-global-conjugate-theorem",
        Laws,
        Plan).
