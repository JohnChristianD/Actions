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
    discovery_egraph_from_laws(Laws, E, QuotientCount),
    CompositeCount = list.length(
        list.filter(
            (pred(L::in) is semidet :-
                semantic_law.composite(L) = yes),
            Laws)),
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
        class_count(E) < enode_count(E)
    ->
        io.write_string(
            "learner-semantic-egraph-regression=pass "
            "source=manifest "
            "quotient=proof-compose-associativity "
            "dynamic=on\n",
            !IO)
    ;
        io.write_string(
            "ERROR: learner semantic e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
