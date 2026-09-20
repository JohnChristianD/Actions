:- module interpolated_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module interpolated_theorem_egraph.
:- import_module learner_semantic_manifest.
:- import_module symbolic_egraph.

main(!IO) :-
    read_manifest(Laws, !IO),
    discovery_egraph_from_laws(Laws, E0, QuotientCount),
    saturate(semantic_rewrite_rules, 32, E0, E, Saturation),
    analyze(E, Analyses),
    add_expr(app("semantic-law", [atom(forced_target_id)]), E, TargetClass, E1),
    extract_best(TargetClass, E1, 64, _, ExtractionCost),
    TargetId = forced_target_id,
    PolicyAttention = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalPolicy-attention-invariant",
    PolicyNorm = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalPolicy-norm-invariant",
    PolicyOptimizer = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalPolicy-optimizer-invariant",
    HardSparse = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#hardSparse-composition-normPair-F4-L2",
    Recurrent = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#canonicalGRU-recurrent-associative-scan-theorem",
    HardSign = "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda#hardSignGate-idempotent",
    NonReflexive = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.reflexive(L) = no),
            Laws)),
    (
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.source(L) =
                    "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda"),
            Laws) = Laws,
        list.member(TargetLaw, Laws),
        law_id(TargetLaw) = TargetId,
        semantic_law.composite(TargetLaw) = yes,
        list.member(PolicyAttention, semantic_law.dependencies(TargetLaw)),
        list.member(PolicyNorm, semantic_law.dependencies(TargetLaw)),
        list.member(PolicyOptimizer, semantic_law.dependencies(TargetLaw)),
        list.member(HardSparse, semantic_law.dependencies(TargetLaw)),
        list.member(Recurrent, semantic_law.dependencies(TargetLaw)),
        list.member(HardSignLaw, Laws),
        law_id(HardSignLaw) = HardSign,
        NonReflexive > 0,
        QuotientCount > 0,
        class_count(E) > 0,
        enode_count(E) > 0,
        class_count(E) < enode_count(E),
        list.length(Analyses) > 0,
        saturation_iterations(Saturation) > 0,
        ExtractionCost > 0,
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
            "theorem-semantic-egraph-regression=pass "
            "source=manifest "
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
