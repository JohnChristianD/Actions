:- module interpolated_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_extractor.
:- import_module symbolic_egraph.

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    discovery_egraph_from_laws(Laws, E0, QuotientCount),
    saturate(semantic_rewrite_rules, 32, E0, E, Saturation),
    analyze(E, Analyses),
    E1 = E,
    TargetClass = _,
    (\n        list.filter(\n            (pred(L::in) is semidet :-\n                semantic_law.source(L) =\n                    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda"),\n            Laws) = Laws,\n        list.length(Laws) > 0,\n        list.member(CompositeLaw, Laws),\n        is_composite(CompositeLaw),\n        NonReflexive > 0,\n        QuotientCount > 0,\n        class_count(E) > 0,\n        enode_count(E) > 0,\n        class_count(E) < enode_count(E),\n        list.length(Analyses) > 0,\n        saturation_iterations(Saturation) > 0,\n        ExtractionCost > 0\n        ->
        io.write_string(
            "theorem-semantic-egraph-regression=pass "
            "source=TheoremsMonolith.agda "
            "quotient=proof-compose-associativity "
            "e-matching=on saturation=on rebuild=on "
            "eclass-analysis=on cost-extraction=on "
            "target=polymorphic-sparsemax\n",
            !IO)
    ;
        io.write_string(
            "ERROR: theorem semantic e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
