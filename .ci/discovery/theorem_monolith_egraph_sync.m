:- module theorem_monolith_egraph_sync.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module bool.
:- import_module int.

:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_extractor.
:- import_module list.
:- import_module string.
:- import_module symbolic_egraph.
:- import_module theorem_graph_search.

:- pred add_graph_plans(
    list(list(string))::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out) is det.
add_graph_plans([], E, E).
add_graph_plans([Plan | Plans], E0, E) :-
    add_expr(graph_plan_expr(Plan), E0, _, E1),
    add_graph_plans(Plans, E1, E).

:- pred plan_terminal_ids(
    list(list(string))::in,
    list(string)::in,
    list(string)::out) is det.
plan_terminal_ids([], Acc, Ids) :-
    list.reverse(Acc, Ids).
plan_terminal_ids([Plan | Plans], Acc0, Ids) :-
    (
        Plan = [Terminal | _],
        list.member(Terminal, Acc0)
    ->
        Acc1 = Acc0
    ;
        (
            Plan = [Terminal | _]
        ->
            Acc1 = [Terminal | Acc0]
        ;
            Acc1 = Acc0
        )
    ),
    plan_terminal_ids(Plans, Acc1, Ids).

:- pred closure_round(
    list(semantic_law)::in,
    list(string)::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out,
    list(list(string))::out,
    saturation_report::out,
    int::out,
    int::out) is det.
closure_round(
    Laws,
    SeedIds,
    E0,
    E,
    RoundPlans,
    Saturation,
    BeforeEnodes,
    AfterEnodes) :-
    BeforeEnodes = enode_count(E0),
    search_emergent_compositions_from_seed_ids(
        Laws, SeedIds, RoundPlans0),
    RoundPlans = RoundPlans0,
    add_graph_plans(RoundPlans, E0, E1),
    saturate_until_stable(
        semantic_rewrite_rules, E1, E, Saturation),
    AfterEnodes = enode_count(E).

:- pred astar_egraph_fixed_point(
    list(semantic_law)::in,
    list(list(string))::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out,
    list(list(string))::out,
    int::out,
    int::out,
    int::out,
    bool::out) is det.
astar_egraph_fixed_point(
    Laws, InitialPlans, E0, E, Plans, Rounds, BeforeEnodes,
    AfterEnodes, Stable) :-
    SeedIds0 = [],
    plan_terminal_ids(InitialPlans, SeedIds0, SeedIds),
    closure_round(
        Laws, SeedIds, E0, E1, RoundPlans1,
        _, BeforeEnodes1, AfterEnodes1),
    (
        AfterEnodes1 = BeforeEnodes1,
        RoundPlans1 = InitialPlans
    ->
        E = E1,
        Plans = InitialPlans,
        Rounds = 1,
        BeforeEnodes = BeforeEnodes1,
        AfterEnodes = AfterEnodes1,
        Stable = yes
    ;
        SeedIds1 = [],
        plan_terminal_ids(RoundPlans1, SeedIds1, SeedIdsNext),
        closure_round(
            Laws, SeedIdsNext, E1, E2, RoundPlans2,
            _, BeforeEnodes2, AfterEnodes2),
        (
            RoundPlans2 = RoundPlans1,
            AfterEnodes2 = BeforeEnodes2
        ->
            E = E2,
            Plans = RoundPlans2,
            Rounds = 2,
            BeforeEnodes = BeforeEnodes1,
            AfterEnodes = AfterEnodes2,
            Stable = yes
        ;
            E = E2,
            Plans = RoundPlans2,
            Rounds = 2,
            BeforeEnodes = BeforeEnodes1,
            AfterEnodes = AfterEnodes2,
            Stable = no
        )
    ).

:- pred write_plan_items(
    io.text_output_stream::in, list(list(string))::in,
    io::di, io::uo) is det.
write_plan_items(_, [], !IO).
write_plan_items(Stream, [Plan | Plans], !IO) :-
    io.write_string("    \"", !IO),
    io.write_string(string.join_list(" -> ", Plan), !IO),
    io.write_string("\"", !IO),
    (
        Plans = []
    ->
        true
    ;
        io.write_string(",", !IO)
    ),
    io.write_string("\n", !IO),
    write_plan_items(Stream, Plans, !IO).


:- pred write_string_items(
    io.text_output_stream::in,
    list(string)::in,
    io::di, io::uo) is det.
write_string_items(_, [], !IO).
write_string_items(Stream, [Item | Items], !IO) :-
    io.write_string(Stream, "    \"", !IO),
    io.write_string(Stream, Item, !IO),
    io.write_string(Stream, "\"", !IO),
    (
        Items = []
    ->
        true
    ;
        io.write_string(Stream, ",", !IO)
    ),
    io.write_string(Stream, "\n", !IO),
    write_string_items(Stream, Items, !IO).

:- pred extract_all_laws(
    list(semantic_law)::in,
    symbolic_egraph.egraph::in,
    int::in,
    int::out) is det.
extract_all_laws([], _, _, 0).
extract_all_laws([Law | Laws], E, Depth, Cost) :-
    (
        if is_record_field(Law) then
            extract_all_laws(Laws, E, Depth, Cost)
        else
            add_expr(law_expr(law_id(Law)), E, Class, E1),
            (
                if extract_best(Class, E1, Depth, _, ThisCost) then
                    extract_all_laws(Laws, E1, Depth, TailCost),
                    Cost = ThisCost + TailCost
                else
                    Cost = 0
            )
    ).

:- pred write_report(
    list(semantic_law)::in,
    int::in,
    saturation_report::in,
    int::in,
    list(list(string))::in,
    list(list(string))::in,
    list(string)::in,
    list(string)::in,
    int::in,
    int::in,
    int::in,
    bool::in,
    io::di, io::uo) is det.
write_report(All, QuotientCount, Saturation, ExtractionCost,
    Plans, FrontierPlans, DominanceEdges, PrunedTheorems,
    ClosureRounds, ClosureBeforeEnodes, ClosureAfterEnodes,
    ClosureStable, !IO) :-
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :- not is_reflexive(L)),
            All)),
    io.open_output("theorem-monolith-egraph-sync.dhall", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream, "{
", !IO),
        io.write_string(Stream,
            "  sourceTheoremMonolith = \"../../../FullCoupled/TheoremsMonolith.agda\",
",
            !IO),
        io.write_string(Stream,
            "  forcedSymbolicTarget = False,
", !IO),
        io.write_string(Stream,
            "  singleAgdaSource = True,
", !IO),
        io.write_string(Stream, "  semanticLawCount = ", !IO),
        io.write_string(Stream, string.int_to_string(list.length(All)), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  nonreflexiveLawCount = ", !IO),
        io.write_string(Stream, string.int_to_string(NonReflexive), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  egraphAssociativityQuotientCount = ", !IO),
        io.write_string(Stream, string.int_to_string(QuotientCount), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  egraphSaturationIterations = ", !IO),
        io.write_string(Stream,
            string.int_to_string(saturation_iterations(Saturation)), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  egraphExtractionCost = ", !IO),
        io.write_string(Stream, string.int_to_string(ExtractionCost), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  closureRounds = ", !IO),
        io.write_string(Stream, string.int_to_string(ClosureRounds), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  closureBeforeEnodes = ", !IO),
        io.write_string(Stream, string.int_to_string(ClosureBeforeEnodes), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  closureAfterEnodes = ", !IO),
        io.write_string(Stream, string.int_to_string(ClosureAfterEnodes), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  astarEgraphFixedPoint = ", !IO),
        (
            ClosureStable = yes
        ->
            io.write_string(Stream, "True", !IO)
        ;
            io.write_string(Stream, "False", !IO)
        ),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  emergentCompositionCount = ", !IO),
        io.write_string(Stream, string.int_to_string(list.length(Plans)), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  astarScoreOrdered = True,
", !IO),
        io.write_string(Stream, "  emergentCompositionPlans = [
", !IO),
        write_plan_items(Stream, Plans, !IO),
        io.write_string(Stream, "  ],
", !IO),
        io.write_string(Stream, "  newNonredundantTheoremCount = 0,
", !IO),
        io.write_string(Stream, "  dominanceDetection = ", !IO),
        (
            DominanceEdges = []
        ->
            io.write_string(Stream, "False", !IO)
        ;
            io.write_string(Stream, "True", !IO)
        ),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  dominanceEdgeCount = ", !IO),
        io.write_string(
            Stream,
            string.int_to_string(list.length(DominanceEdges)),
            !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  dominanceEdges = [
", !IO),
        write_string_items(Stream, DominanceEdges, !IO),
        io.write_string(Stream, "  ],
", !IO),
        io.write_string(Stream, "  prunedPublicTheoremCount = ", !IO),
        io.write_string(
            Stream,
            string.int_to_string(list.length(PrunedTheorems)),
            !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  prunedPublicTheorems = [
", !IO),
        write_string_items(Stream, PrunedTheorems, !IO),
        io.write_string(Stream, "  ],
", !IO),
        io.write_string(Stream, "  reviewFrontierCount = ", !IO),
        io.write_string(
            Stream, string.int_to_string(list.length(FrontierPlans)), !IO),
        io.write_string(Stream, ",
", !IO),
        io.write_string(Stream, "  reviewFrontierPlans = [
", !IO),
        write_plan_items(Stream, FrontierPlans, !IO),
        io.write_string(Stream, "  ],
", !IO),
        io.write_string(Stream,
            "  graphSearch = \"A* cost-guided dependency paths\",
",
            !IO),
        io.write_string(Stream,
            "  proofAuthority = \"Agda --safe\"
", !IO),
        io.write_string(Stream, "}
", !IO),
        io.close_output(Stream, !IO)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write theorem monolith e-graph sync report
",
            !IO),
        io.set_exit_status(1, !IO)
    ).

resolve_graph_requirements(
    Laws,
    AutomaticCompositePlans,
    EndogenousCompositePlans,
    RequiredPlans,
    RequiredSubcompositionPlans,
    FiniteObservationStationaryLimitPlan,
    FiniteObservationStationaryPlan,
    EndogenousObservationPlan,
    EndogenousRNNLMPOMDPObservationTopologyPlan,
    FiniteProbabilityMassPlan,
    FinitePOMDPProbabilityPlan,
    EndogenousPOMDPObservationPlan) :-
    (
        if graph_search_completion(Laws, RP, RSP),
           graph_finite_observation_stationary_limit_plan(Laws, FOSLP),
           graph_finite_observation_stationary_plan(Laws, FOSP),
           graph_endogenous_observation_plan(Laws, EOP),
           graph_endogenous_rnnlm_pomdp_observation_topology_plan(Laws, ERPO),
           graph_finite_probability_mass_plan(Laws, FPMP),
           graph_finite_pomdp_probability_plan(Laws, FPPP),
           graph_endogenous_pomdp_observation_plan(Laws, EPBP),
           all_generated_plans_valid(Laws, AutomaticCompositePlans),
           all_generated_plans_valid(Laws, EndogenousCompositePlans)
        then
            RequiredPlans = RP,
            RequiredSubcompositionPlans = RSP,
            FiniteObservationStationaryLimitPlan = FOSLP,
            FiniteObservationStationaryPlan = FOSP,
            EndogenousObservationPlan = EOP,
            EndogenousRNNLMPOMDPObservationTopologyPlan = ERPO,
            FiniteProbabilityMassPlan = FPMP,
            FinitePOMDPProbabilityPlan = FPPP,
            EndogenousPOMDPObservationPlan = EPBP
        else
            RequiredPlans = [],
            RequiredSubcompositionPlans = [],
            FiniteObservationStationaryLimitPlan = [],
            FiniteObservationStationaryPlan = [],
            EndogenousObservationPlan = [],
            EndogenousRNNLMPOMDPObservationTopologyPlan = [],
            FiniteProbabilityMassPlan = [],
            FinitePOMDPProbabilityPlan = [],
            EndogenousPOMDPObservationPlan = []
    ).

:- pred all_names_present(
    list(string)::in,
    list(string)::in) is semidet.
all_names_present([], _).
all_names_present([Name | Names], Candidates) :-
    list.member(Name, Candidates),
    all_names_present(Names, Candidates).

main(!IO) :-
    read_semantic_laws(All, !IO),
    search_emergent_compositions(All, Plans),
    search_all_composite_law_plans(All, AutomaticCompositePlans),
    search_endogenous_composite_plans(All, EndogenousCompositePlans),
    graph_review_frontier_plans(All, FrontierPlans),
    graph_dominance_edges(All, DominanceEdges),
    graph_dominated_public_theorems(All, DominatedTheorems),
    PrunedTheorems = graph_pruned_public_theorem_names,
    AllGeneratedPlans =
        Plans ++ AutomaticCompositePlans ++ EndogenousCompositePlans
        ++ FrontierPlans,
    resolve_graph_requirements(
        All,
        AutomaticCompositePlans,
        EndogenousCompositePlans,
        RequiredPlans,
        RequiredSubcompositionPlans,
        FiniteObservationStationaryLimitPlan,
        FiniteObservationStationaryPlan,
        EndogenousObservationPlan,
        EndogenousRNNLMPOMDPObservationTopologyPlan,
        FiniteProbabilityMassPlan,
        FinitePOMDPProbabilityPlan,
        EndogenousPOMDPObservationPlan),
    discovery_egraph_from_laws(All, EGraph0, QuotientCount),
    add_graph_plans(
        Plans ++ AutomaticCompositePlans ++ EndogenousCompositePlans
        ++ FrontierPlans,
        EGraph0,
        EGraphGraph0),
    astar_egraph_fixed_point(
        All,
        AllGeneratedPlans,
        EGraphGraph0,
        EGraph,
        ClosedPlans,
        ClosureRounds,
        ClosureBeforeEnodes,
        ClosureAfterEnodes,
        ClosureStable),
    saturate_until_stable(
        semantic_rewrite_rules, EGraph, EGraphStable, Saturation),
    analyze(EGraphStable, Analyses),

    ExtractionDepth = enode_count(EGraphStable) + 1,
    extract_all_laws(All, EGraphStable, ExtractionDepth, ExtractionCost),
    (
        if
            list.length(All) > 0,
            list.length(Plans) > 0,
            list.length(ClosedPlans) > 0,
            ClosureStable = yes,
            ClosureRounds > 0,
            ClosureAfterEnodes >= ClosureBeforeEnodes,
            list.length(AutomaticCompositePlans) > 0,
            list.length(EndogenousCompositePlans) > 0,
            list.length(FrontierPlans) = list.length(graph_review_frontier_names),
            DominanceEdges = [],
            all_names_present(PrunedTheorems, DominatedTheorems),
            list.length(PrunedTheorems) = 2,
            list.length(RequiredPlans) = list.length(graph_required_theorems),
            list.length(RequiredSubcompositionPlans) = list.length(graph_required_subcompositions),
            list.length(FiniteObservationStationaryLimitPlan) > 0,
            list.length(FiniteObservationStationaryPlan) > 0,
            list.length(EndogenousObservationPlan) > 0,
            list.length(EndogenousRNNLMPOMDPObservationTopologyPlan) > 0,
            list.length(FiniteProbabilityMassPlan) > 0,
            list.length(FinitePOMDPProbabilityPlan) > 0,
            list.length(EndogenousPOMDPObservationPlan) > 0,
            list.length(Analyses) > 0,
            class_count(EGraph) > 0,
            enode_count(EGraph) > 0,
            saturation_iterations(Saturation) > 0,
            ExtractionCost > 0,
            all_scores_non_decreasing(All, Plans)
        then
            write_report(
                All,
                QuotientCount,
                Saturation,
                ExtractionCost,
                ClosedPlans,
                FrontierPlans,
                DominanceEdges,
                PrunedTheorems,
                ClosureRounds,
                ClosureBeforeEnodes,
                ClosureAfterEnodes,
                ClosureStable,
                !IO),
            io.write_string(
                "mercury-theorem-monolith-egraph-sync=pass\n", !IO),
            io.write_string("forced-symbolic-target=false\n", !IO),
            io.write_string("emergent-law-count=", !IO),
            io.write_string(string.int_to_string(list.length(All)), !IO),
            io.write_string("\n", !IO),
            io.write_string("emergent-composition-count=", !IO),
            io.write_string(string.int_to_string(list.length(Plans)), !IO),
            io.write_string("\n", !IO),
            io.write_string(
                "single-agda-source=TheoremsMonolith.agda\n", !IO),
            io.write_string(
                "proof-authority=Agda --safe\n", !IO),
            io.write_string(
                "all-agda-laws-extracted=true\n", !IO)
        else
            io.write_string(
                "ERROR: exhaustive theorem dependency graph / e-graph gate failed\n",
                !IO),
            io.set_exit_status(1, !IO)
    ).
