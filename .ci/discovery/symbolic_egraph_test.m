:- module symbolic_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module symbolic_egraph.
:- import_module list.
:- import_module string.


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
        Rewrite = rewrite_rule(
            "proof-compose-associativity",
            papp("proof-compose", [
                pvar("A"),
                papp("proof-compose", [pvar("B"), pvar("C")])
            ]),
            papp("proof-compose", [
                papp("proof-compose", [pvar("A"), pvar("B")]),
                pvar("C")
            ])),
        add_expr(
            app("proof-compose", [
                atom("a"),
                app("proof-compose", [atom("b"), atom("c")])
            ]),
            E5, Nested, E6),
        add_expr(
            app("proof-compose", [
                app("proof-compose", [atom("a"), atom("b")]),
                atom("c")
            ]),
            E6, Left, E7),
        saturate_until_stable([Rewrite], E7, E8, Sat),
        (
            equivalent(Nested, Left, E8),
            e_match(
                papp("proof-compose", [
                    pvar("X"),
                    papp("proof-compose", [pvar("Y"), pvar("Z")])
                ]),
                Nested,
                E8,
                _
            ),
            analyze(E8, Analyses),
            list.length(Analyses) > 0,
            extract_best(Nested, E8, 32, Extracted, Cost),
            Cost > 0,
            (Extracted = atom(_) ; Extracted = app(_, _))
        ->
            io.write_string(
                "symbolic-egraph-regression=pass "
                "hash-cons=on "
                "congruence-closure=on "
                "e-matching=on "
                "saturation=on "
                "rebuild=on "
                "eclass-analysis=on "
                "cost-extraction=on "
                "iterations=" ++
                string.int_to_string(saturation_iterations(Sat)) ++
                "\n",
                !IO)
        ;
            io.write_string(
                "ERROR: equality-saturation semantic e-graph regression failed\n",
                !IO),
            io.set_exit_status(1, !IO)
        )
    ;
        io.write_string(
            "ERROR: symbolic e-graph congruence regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
