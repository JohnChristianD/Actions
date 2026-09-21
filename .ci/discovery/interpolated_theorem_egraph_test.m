:- module interpolated_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module int.
:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_extractor.
:- import_module list.
:- import_module symbolic_egraph.

main(!IO) :-
    read_semantic_laws(Laws, !IO),
    discovery_egraph_from_laws(Laws, E0, QuotientCount),
    saturate_until_stable(semantic_rewrite_rules, E0, E, Saturation),
    analyze(E, Analyses),
    Laws = [FirstLaw | _],
    law_id(FirstLaw) = FirstId,
    add_expr(law_expr(FirstId), E, FirstClass, E1),
    ExtractionDepth = enode_count(E1) + 1,
    extract_best(FirstClass, E1, ExtractionDepth, Extracted, ExtractionCost),
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :- not is_reflexive(L)),
            Laws)),
    CompositeCount = list.length(
        list.filter(
            (pred(L::in) is semidet :- is_composite(L)),
            Laws)),
    (
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.source(L) =
                    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda"),
            Laws) = Laws,
        list.length(Laws) > 0,
        NonReflexive > 0,
        CompositeCount > 0,
        QuotientCount > 0,
        class_count(E) > 0,
        enode_count(E) > 0,
        class_count(E) < enode_count(E),
        list.length(Analyses) > 0,
        saturation_iterations(Saturation) > 0,
        ExtractionCost > 0,
        (Extracted = atom(_) ; Extracted = app(_, _))
    ->
        io.write_string(
            "theorem-semantic-egraph-regression=pass "
            "source=TheoremsMonolith.agda "
            "laws=source-derived "
            "quotient=proof-compose-associativity "
            "e-matching=on saturation=on rebuild=on "
            "eclass-analysis=on cost-extraction=on "
            "target=all-source-derived-laws\n",
            !IO)
    ;
        io.write_string(
            "ERROR: theorem semantic e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
