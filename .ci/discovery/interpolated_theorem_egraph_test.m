:- module interpolated_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module symbolic_egraph.
:- import_module interpolated_theorem_egraph.

main(!IO) :-
    discovery_egraph(E, !IO),
    (
        class_count(E) > 0,
        enode_count(E) > 0,
        class_count(E) =< enode_count(E)
    ->
        io.write_string(
            "learner-semantic-egraph-regression=pass "
            "source=monolith "
            "composition=extracted "
            "refl=noncomposition\n",
            !IO)
    ;
        io.write_string(
            "ERROR: learner semantic e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
