:- module theorem_monolith_egraph_sync.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_extractor.
:- import_module learner_semantic_manifest.
:- import_module list.
:- import_module string.
:- import_module symbolic_egraph.
:- import_module theorem_astar_search.

:- pred law_for_id(
    string::in, list(semantic_law)::in, semantic_law::out) is semidet.
law_for_id(Id, Laws, Law) :-
    list.member(Law, Laws),
    law_id(Law) = Id.

:- pred plan_seed_id(list(string)::in, string::out) is semidet.
plan_seed_id(Plan, SeedId) :-
    list.reverse(Plan, Reversed),
    Reversed = [SeedId | _].

:- pred selected_emergent_law(
    list(list(string))::in,
    list(semantic_law)::in,
    semantic_law::out) is semidet.
selected_emergent_law([Plan | _], Laws, Law) :-
    plan_seed_id(Plan, SeedId),
    law_for_id(SeedId, Laws, Law).

:- pred add_astar_plans(
    list(list(string))::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out) is det.
add_astar_plans([], E, E).
add_astar_plans([Plan | Plans], E0, E) :-
    add_expr(astar_plan_expr(Plan), E0, _, E1),
    add_astar_plans(Plans, E1, E).

:- pred dependency_chain_valid(
    list(string)::in, list(semantic_law)::in) is semidet.
dependency_chain_valid([_], _) :- semidet_fail.
dependency_chain_valid([Dependency, Parent | Rest], Laws) :-
    law_for_id(Parent, Laws, ParentLaw),
    list.member(Dependency, law_dependencies(ParentLaw)),
    (
        Rest = []
    ->
        true
    ;
        dependency_chain_valid([Parent | Rest], Laws)
    ).

:- pred astar_plan_valid(
    list(string)::in, list(semantic_law)::in) is semidet.
astar_plan_valid(Plan, Laws) :-
    list.length(Plan) >= 3,
    all_unique(Plan, Laws),
    all_nonreflexive(Plan, Laws),
    dependency_chain_valid(Plan, Laws),
    list.reverse(Plan, [_Terminal | [SeedId | _]]),
    law_for_id(SeedId, Laws, SeedLaw),
    Plan = [TerminalId | _],
    not list.member(TerminalId, law_dependencies(SeedLaw)).

:- pred all_unique(list(string)::in, list(semantic_law)::in) is semidet.
all_unique([], _).
all_unique([Id | Ids], Laws) :-
    not list.member(Id, Ids),
    law_for_id(Id, Laws, _),
    all_unique(Ids, Laws).

:- pred all_nonreflexive(list(string)::in, list(semantic_law)::in) is semidet.
all_nonreflexive([], _).
all_nonreflexive([Id | Ids], Laws) :-
    law_for_id(Id, Laws, Law),
    not is_reflexive(Law),
    all_nonreflexive(Ids, Laws).

:- pred all_astar_plans_valid(
    list(list(string))::in, list(semantic_law)::in) is semidet.
all_astar_plans_valid([], _).
all_astar_plans_valid([Plan | Plans], Laws) :-
    astar_plan_valid(Plan, Laws),
    all_astar_plans_valid(Plans, Laws).

:- pred write_plan_items(
    io.output_stream::in, list(list(string))::in,
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


:- pred write_report(
    list(semantic_law)::in,
    semantic_law::in,
    int::in,
    saturation_report::in,
    int::in,
    list(list(string))::in,
    io::di, io::uo) is det.
write_report(All, Target, QuotientCount, Saturation, ExtractionCost,
    AStarPlans, !IO) :-
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :- not is_reflexive(L)),
            All)),
    io.open_output("theorem-monolith-egraph-sync.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream, "{\n", !IO),
        io.write_string(Stream,
            "  \"source_theorem_monolith\": \"../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda\",\n",
            !IO),
        io.write_string(Stream,
            "  \"forced_symbolic_target\": false,\n", !IO),
        io.write_string(Stream,
            "  \"selected_emergent_law\": \"", !IO),
        io.write_string(Stream, law_id(Target), !IO),
        io.write_string(Stream, "\",\n", !IO),
        io.write_string(Stream, "  \"single_agda_source\": true,\n", !IO),
        io.write_string(Stream, "  \"semantic_law_count\": ", !IO),
        io.write_string(Stream, string.int_to_string(list.length(All)), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"nonreflexive_law_count\": ", !IO),
        io.write_string(Stream, string.int_to_string(NonReflexive), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"egraph_associativity_quotient_count\": ", !IO),
        io.write_string(Stream, string.int_to_string(QuotientCount), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"egraph_saturation_iterations\": ", !IO),
        io.write_string(Stream,
            string.int_to_string(saturation_iterations(Saturation)), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"egraph_extraction_cost\": ", !IO),
        io.write_string(Stream, string.int_to_string(ExtractionCost), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"astar_emergent_candidate_count\": ", !IO),
        io.write_string(Stream, string.int_to_string(list.length(AStarPlans)), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"astar_candidate_plans\": [\n", !IO),
        write_plan_items(Stream, AStarPlans, !IO),
        io.write_string(Stream, "  ],\n", !IO),
        io.write_string(Stream,
            "  \"astar_search\": \"structural dependency composition only\",\n",
            !IO),
        io.write_string(Stream,
            "  \"proof_authority\": \"Agda --safe\"\n", !IO),
        io.write_string(Stream, "}\n", !IO),
        io.close_output(Stream, !IO)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write theorem monolith e-graph sync report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    extract_semantics(!IO),
    read_manifest(All, !IO),
    search_emergent_compositions(All, 8, AStarPlans, !IO),
    (
        selected_emergent_law(AStarPlans, All, Target),
        discovery_egraph_from_laws(All, EGraph0, QuotientCount),
        add_astar_plans(AStarPlans, EGraph0, EGraphAStar),
        saturate(semantic_rewrite_rules, 32, EGraphAStar, EGraph, Saturation),
        analyze(EGraph, Analyses),
        add_expr(law_expr(law_id(Target)), EGraph, TargetClass, EGraph1),
        extract_best(TargetClass, EGraph1, 64, _, ExtractionCost),
        list.length(All) > 0,
        list.length(AStarPlans) > 0,
        all_astar_plans_valid(AStarPlans, All),
        list.length(Analyses) > 0,
        QuotientCount > 0,
        class_count(EGraph) > 0,
        enode_count(EGraph) > 0,
        saturation_iterations(Saturation) > 0,
        ExtractionCost > 0
    ->
        write_report(All, Target, QuotientCount, Saturation,
            ExtractionCost, AStarPlans, !IO),
        io.write_string(
            "mercury-theorem-monolith-egraph-sync=pass\n", !IO),
        io.write_string("forced-symbolic-target=false\n", !IO),
        io.write_string("selected-emergent-law=", !IO),
        io.write_string(law_id(Target), !IO),
        io.write_string("\n", !IO),
        io.write_string("astar-emergent-candidate-count=", !IO),
        io.write_string(string.int_to_string(list.length(AStarPlans)), !IO),
        io.write_string("\n", !IO),
        io.write_string(
            "single-agda-source=TheoremsMonolith.agda\n", !IO),
        io.write_string(
            "proof-authority=Agda --safe\n", !IO)
    ;
        io.write_string(
            "ERROR: structural A* / e-graph gate failed\n", !IO),
        io.set_exit_status(1, !IO)
    ).
