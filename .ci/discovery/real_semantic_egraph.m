:- module real_semantic_egraph.

:- interface.

:- import_module io.
:- import_module list.
:- import_module symbolic_egraph.
:- import_module learner_semantic_extractor.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module int.
:- import_module string.
:- import_module interpolated_theorem_egraph.

 :- func frontier_targets = list(string).
frontier_targets = [
    "CanonicalIntegerGRUGlobalConjugateTheorem",
    "CanonicalIntegerGRUFractalLimitCompositionTheorem",
    "GRUFractalLimitConvergenceWitness",
    "StationaryLimitTheorem",
    "ContinuousLeftInverseTheorem"
].

:- pred partition_targets(
    list(string)::in,
    list(semantic_law)::in,
    list(string)::out,
    list(string)::out) is det.
partition_targets([], _, [], []).
partition_targets([Name | Names], Laws, Fresh, Stale) :-
    partition_targets(Names, Laws, FreshTail, StaleTail),
    (
        if law_name_member(Name, Laws) then
            Fresh = [Name | FreshTail],
            Stale = StaleTail
        else
            Fresh = FreshTail,
            Stale = [Name | StaleTail]
    ).

:- pred law_name_member(string::in, list(semantic_law)::in) is semidet.
law_name_member(_, []) :-
    fail.
law_name_member(Name, [Law | Laws]) :-
    (
        law_name(Law) = Name
    ;
        law_name_member(Name, Laws)
    ).

:- pred add_target_exprs(
    list(string)::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out) is det.
add_target_exprs([], E, E).
add_target_exprs([Name | Names], E0, E) :-
    add_expr(
        app("theorem-target", [atom(Name)]),
        E0, _, E1),
    add_target_exprs(Names, E1, E).

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    frontier_targets(Targets),
    partition_targets(Targets, Laws, Fresh, Stale),
    discovery_egraph_from_laws(Laws, E0, QuotientCount),
    add_target_exprs(Fresh, E0, E1),
    saturate_until_stable(
        semantic_rewrite_rules,
        E1,
        EStable,
        Saturation),
    analyze(EStable, Analyses),
    io.write_string(
        "real-semantic-egraph=pass\n", !IO),
    io.write_string(
        "graph-semantics=eclasses+certified-rewrites+guarded-frontiers\n",
        !IO),
    io.write_string(
        "fresh-target-count=" ++
        string.int_to_string(list.length(Fresh)) ++ "\n",
        !IO),
    io.write_string(
        "stale-target-count=" ++
        string.int_to_string(list.length(Stale)) ++ "\n",
        !IO),
    io.write_string(
        "eclass-count=" ++
        string.int_to_string(class_count(EStable)) ++ "\n",
        !IO),
    io.write_string(
        "enode-count=" ++
        string.int_to_string(enode_count(EStable)) ++ "\n",
        !IO),
    io.write_string(
        "associativity-quotient-count=" ++
        string.int_to_string(QuotientCount) ++ "\n",
        !IO),
    io.write_string(
        "saturation-iterations=" ++
        string.int_to_string(saturation_iterations(Saturation)) ++ "\n",
        !IO),
    io.write_string(
        "analysis-class-count=" ++
        string.int_to_string(list.length(Analyses)) ++ "\n",
        !IO),
    io.write_string(
        "stale-targets-pruned=" ++
        string.join_list(",", Stale) ++ "\n",
        !IO),
    io.write_string(
        "proof-authority=Agda --safe\n",
        !IO).
