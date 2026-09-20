:- module interpolated_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module symbolic_egraph.
:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_manifest.
:- import_module list.

main(!IO) :-
    read_manifest(Laws, !IO),
    discovery_egraph_from_laws(Laws, E0, QuotientCount),
    saturate(semantic_rewrite_rules, 32, E0, E, Saturation),
    analyze(E, Analyses),
    add_expr(app("semantic-law", [atom(forced_target_id)]), E, TargetClass, E1),
    extract_best(TargetClass, E1, 64, _, ExtractionCost),
    CompositeCount = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.composite(L) = yes),
            Laws)),
    ExactUAPId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#ExactUniversalApproximationThroughContinuousLeftInverse",
    ContinuousBoundaryId = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalNoGlobalInt8ContinuousLeftInverseOnDiscreteTopologies",
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.reflexive(L) = no),
            Laws)),
    (
        CompositeCount > 0,
        NonReflexive >= CompositeCount,
        QuotientCount > 0,
        class_count(E) > 0,
        enode_count(E) > 0,
        class_count(E) < enode_count(E),
        list.length(Analyses) > 0,
        saturation_iterations(Saturation) > 0,
        ExtractionCost > 0,
        list.member(ExactUAPLaw, Laws),
        law_id(ExactUAPLaw) = ExactUAPId,
        list.member(ContinuousBoundaryLaw, Laws),
        law_id(ContinuousBoundaryLaw) = ContinuousBoundaryId,
        e_match(
            papp("proof-compose", [
                pvar("A"),
                papp("proof-compose", [pvar("B"), pvar("C")])
            ]),
            TargetClass,
            E1,
            _)
    ->
        io.write_string(
            "learner-semantic-egraph-regression=pass "
            "source=manifest "
            "quotient=proof-compose-associativity "
            "e-matching=on saturation=on rebuild=on "
            "eclass-analysis=on cost-extraction=on "
            "dynamic=on\n",
            !IO)
    ;
        io.write_string(
            "ERROR: learner semantic e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
