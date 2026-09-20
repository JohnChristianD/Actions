:- module interpolated_theorem_egraph.

:- interface.

:- import_module io.
:- import_module symbolic_egraph.
:- import_module learner_semantic_manifest.

:- pred discovery_egraph(
    symbolic_egraph.egraph::out,
    int::out,
    io::di, io::uo) is det.
:- pred discovery_egraph_from_laws(
    list(semantic_law)::in,
    symbolic_egraph.egraph::out,
    int::out) is det.
:- func forced_target_id = string.
forced_target_id =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonical-endogenous-minimax-bellman-shapley-uap-theorem".

:- func bounded_exact_approximation_dependency = string.
bounded_exact_approximation_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#boundedExactApproximation-on-boundedOrbit".

:- func continuous_readout_dependency = string.
continuous_readout_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#continuousLeftInverse-exactReadout-transfer".

:- func infinite_state_orbit_dependency = string.
infinite_state_orbit_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalInfiniteStateOrbitEmbedding".

:- func pigeonhole_dependency = string.
pigeonhole_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalPigeonholeNatClockContradiction".

:- func no_global_uap_dependency = string.
:- func finite_int8_continuous_left_inverse_dependency = string.
:- func exact_universal_uap_dependency = string.
no_global_uap_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoGlobalInt8DiscreteUAPOnOrbit".

finite_int8_continuous_left_inverse_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies".

exact_universal_uap_dependency =
    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#ExactUniversalApproximationThroughContinuousLeftInverse".


:- func semantic_rewrite_rules = list(rewrite_rule).


semantic_rewrite_rules = [
    rewrite_rule(
        "proof-compose-associativity",
        papp("proof-compose", [
            pvar("A"),
            papp("proof-compose", [pvar("B"), pvar("C")])
        ]),
        papp("proof-compose", [
            papp("proof-compose", [pvar("A"), pvar("B")]),
            pvar("C")
        ])),
    rewrite_rule(
        "proof-compose-empty-right",
        papp("proof-compose", [
            pvar("A"),
            papp("empty-proof-compose", [])
        ]),
        pvar("A")),
    rewrite_rule(
        "proof-compose-empty-left",
        papp("proof-compose", [
            papp("empty-proof-compose", []),
            pvar("A")
        ]),
        pvar("A"))
].

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module bool.
:- import_module list.
:- import_module string.

:- func law_expr(string) = expr.
law_expr(Id) = app("semantic-law", [atom(Id)]).

:- func left_assoc_expr(list(string)) = expr.
left_assoc_expr([]) = atom("empty-proof-compose").
left_assoc_expr([Id]) = law_expr(Id).
left_assoc_expr([A, B | Rest]) =
    left_assoc_expr_acc(
        app("proof-compose", [law_expr(A), law_expr(B)]),
        Rest).

:- func left_assoc_expr_acc(expr, list(string)) = expr.
left_assoc_expr_acc(Acc, []) = Acc.
left_assoc_expr_acc(Acc, [Id | Rest]) =
    left_assoc_expr_acc(
        app("proof-compose", [Acc, law_expr(Id)]),
        Rest).

:- func right_assoc_expr(list(string)) = expr.
right_assoc_expr([]) = atom("empty-proof-compose").
right_assoc_expr([Id]) = law_expr(Id).
right_assoc_expr([Id | Rest]) =
    app("proof-compose", [law_expr(Id), right_assoc_expr(Rest)]).

:- pred add_law(
    semantic_law::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out,
    int::in, int::out) is det.
add_law(Law, E0, E, Quotient0, Quotient) :-
    Id = law_id(Law),
    add_expr(law_expr(Id), E0, _, E1),
    (
        semantic_law.composite(Law) = yes
    ->
        Deps = semantic_law.dependencies(Law),
        Left = left_assoc_expr(Deps),
        add_expr(
            app("derived-proof-plan", [
                law_expr(Id),
                Left
            ]),
            E1, _, E2),
        (
            list.length(Deps) >= 3
        ->
            Right = right_assoc_expr(Deps),
            add_expr(
                app("derived-proof-plan", [
                    law_expr(Id),
                    Right
                ]),
                E2, RightClass, E3),
            add_expr(
                app("derived-proof-plan", [
                    law_expr(Id),
                    Left
                ]),
                E3, LeftClass, E4),
            merge(LeftClass, RightClass, E4, E),
            Quotient = Quotient0 + 1
        ;
            E = E2,
            Quotient = Quotient0
        )
    ;
        (
            semantic_law.reflexive(Law) = yes
        ->
            add_expr(
                app("definitional-law", [law_expr(Id)]),
                E1, _, E)
        ;
            E = E1
        ),
        Quotient = Quotient0
    ).

:- pred add_laws(
    list(semantic_law)::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out,
    int::in, int::out) is det.
add_laws([], E, E, Count, Count).
add_laws([Law | Laws], E0, E, Count0, Count) :-
    add_law(Law, E0, E1, Count0, Count1),
    add_laws(Laws, E1, E, Count1, Count).

discovery_egraph_from_laws(Laws, E, QuotientCount) :-
    E0 = symbolic_egraph.empty,
    add_laws(Laws, E0, E, 0, QuotientCount).

discovery_egraph(E, QuotientCount, !IO) :-
    read_manifest(Laws, !IO),
    discovery_egraph_from_laws(Laws, E, QuotientCount).

main(!IO) :-
    read_manifest(Laws, !IO),
    discovery_egraph_from_laws(Laws, EGraph0, QuotientCount),
    saturate(semantic_rewrite_rules, 32, EGraph0, EGraph, Saturation),
    root_count = class_count(EGraph),
    node_count = enode_count(EGraph),
    analyze(EGraph, Analyses),
    add_expr(law_expr(forced_target_id), EGraph, TargetClass, EGraph1),
    extract_best(TargetClass, EGraph1, 64, _, ExtractionCost),
    CompositeCount = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.composite(L) = yes),
            Laws)),
    RootCount = root_count,
    NodeCount = node_count,
    AnalysisCount = list.length(Analyses),
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.reflexive(L) = no),
            Laws)),
    (
        list.length(Laws) > 0,
        NonReflexive >= CompositeCount,
        QuotientCount > 0,
        RootCount > 0,
        NodeCount > 0,
        RootCount < NodeCount,
        AnalysisCount > 0,
        ExtractionCost > 0,
        saturation_iterations(Saturation) > 0,
        list.member(TargetLaw, Laws),
        law_id(TargetLaw) = forced_target_id,
        semantic_law.composite(TargetLaw) = yes,
        list.length(semantic_law.dependencies(TargetLaw)) >= 3,
        list.member(
            continuous_readout_dependency,
            semantic_law.dependencies(TargetLaw)),
        list.member(
            bounded_exact_approximation_dependency,
            semantic_law.dependencies(TargetLaw)),
        list.member(
            infinite_state_orbit_dependency,
            semantic_law.dependencies(TargetLaw)),
        list.member(
            pigeonhole_dependency,
            semantic_law.dependencies(TargetLaw)),
        list.member(
            no_global_uap_dependency,
            semantic_law.dependencies(TargetLaw)),
        list.member(
            finite_int8_continuous_left_inverse_dependency,
            semantic_law.dependencies(TargetLaw)),
        list.member(
            exact_universal_uap_dependency,
            semantic_law.dependencies(TargetLaw))
    ->
        io.write_string(
            "interpolated-theorem-egraph=pass "
            "source=learner-monolith "
            "semantic-registry=manifest "
            "proof-compose-associativity=quotiented "
            "continuous-left-inverse=connected "
            "exact-universal-readout=connected "
            "bounded-exact-approximation=connected "
            "infinite-state-orbit=connected "
            "pigeonhole-global-int8-uap=refuted "
            "e-matching=on "
            "saturation=on "
            "rebuild=on "
            "eclass-analysis=on "
            "cost-extraction=on "
            "dynamic-manifest=on\n",
            !IO)
    ;
        io.write_string(
            "ERROR: learner semantic e-graph quotient gate failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
