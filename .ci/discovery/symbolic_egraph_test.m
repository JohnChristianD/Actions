:- module symbolic_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module symbolic_egraph.

main(!IO) :-
    E0 = empty,
    add_expr(atom("a"), E0, A, E1),
    add_expr(atom("b"), E1, B, E2),
    add_expr(app("f", [atom("a")]), E2, FA, E3),
    add_expr(app("f", [atom("b")]), E3, FB, E4),
    merge(A, B, E4, E5),
    (
        equivalent(FA, FB, E5)
    ->
        io.write_string(
            "symbolic-egraph-regression=pass hash-cons=on congruence-closure=on\n",
            !IO)
    ;
        io.write_string(
            "ERROR: symbolic e-graph congruence regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
