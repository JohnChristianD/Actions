:- module theorem_monolith_egraph_sync.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module int.

:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_extractor.
:- import_module list.
:- import_module string.
:- import_module symbolic_egraph.
:- import_module theorem_astar_search.

:- pred add_astar_plans(
    list(list(string))::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out) is det.
add_astar_plans([], E, E).
add_astar_plans([Plan | Plans], E0, E) :-
    add_expr(astar_plan_expr(Plan), E0, _, E1),
    add_astar_plans(Plans, E1, E).

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


:- pred extract_all_laws(
    list(semantic_law)::in,
    symbolic_egraph.egraph::in,
    int::in,
    int::out) is semidet.
extract_all_laws([], _, _, 0).
extract_all_laws([Law | Laws], E, Depth, Cost) :-
    add_expr(law_expr(law_id(Law)), E, Class, E1),
    extract_best(Class, E1, Depth, _, ThisCost),
    extract_all_laws(Laws, E1, Depth, TailCost),
    Cost = ThisCost + TailCost.

:- pred write_report(
    list(semantic_law)::in,
    int::in,
    saturation_report::in,
    int::in,
    list(list(string))::in,
    io::di, io::uo) is det.
write_report(All, QuotientCount, Saturation, ExtractionCost,
    Plans, !IO) :-
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
            "  \"single_agda_source\": true,\n", !IO),
        io.write_string(Stream, "  \"semantic_law_count\": ", !IO),
        io.write_string(Stream, string.int_to_string(list.length(All)), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"nonreflexive_law_count\": ", !IO),
        io.write_string(Stream, string.int_to_string(NonReflexive), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream,
            "  \"egraph_associativity_quotient_count\": ", !IO),
        io.write_string(Stream, string.int_to_string(QuotientCount), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"egraph_saturation_iterations\": ", !IO),
        io.write_string(Stream,
            string.int_to_string(saturation_iterations(Saturation)), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"egraph_extraction_cost\": ", !IO),
        io.write_string(Stream, string.int_to_string(ExtractionCost), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"emergent_composition_count\": ", !IO),
        io.write_string(Stream, string.int_to_string(list.length(Plans)), !IO),
        io.write_string(Stream, ",\n", !IO),
        io.write_string(Stream, "  \"emergent_composition_plans\": [\n", !IO),
        write_plan_items(Stream, Plans, !IO),
        io.write_string(Stream, "  ],\n", !IO),
        io.write_string(Stream,
            "  \"graph_search\": \"exhaustive simple dependency paths\",\n",
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
    read_semantic_laws(All, !IO),
    search_emergent_compositions(All, Plans, !IO),
    discovery_egraph_from_laws(All, EGraph0, QuotientCount),
    add_astar_plans(Plans, EGraph0, EGraphAStar),
    saturate(semantic_rewrite_rules, 32, EGraphAStar, EGraph, Saturation),
    analyze(EGraph, Analyses),
    ExtractionDepth = enode_count(EGraph) + 1,
    extract_all_laws(All, EGraph, ExtractionDepth, ExtractionCost),
    list.length(All) > 0,
    list.length(Plans) > 0,
    list.length(Analyses) > 0,
    QuotientCount > 0,
    class_count(EGraph) > 0,
    enode_count(EGraph) > 0,
    saturation_iterations(Saturation) > 0,
    ExtractionCost > 0
    ->
        write_report(
            All,
            QuotientCount,
            Saturation,
            ExtractionCost,
            Plans,
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
            "proof-authority=Agda --safe\n", !IO)
    ;
        io.write_string(
            "ERROR: exhaustive theorem dependency graph / e-graph gate failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
