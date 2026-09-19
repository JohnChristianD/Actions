:- module interpolated_theorem_egraph_test.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module symbolic_egraph.
:- import_module interpolated_theorem_egraph.

main(!IO) :-
    E = discovery_egraph,
    (
        registry_gate,
        raw_goal_count = 5,
        saturated_goal_count = 5,
        enode_count(E) > 5,
        class_count(E) > 0
    ->
        io.write_string(
            "interpolated-theorem-egraph-regression=pass "
            "goals=5 proof-plans=5 registry=validated "
            "composition=nonreflexive\n",
            !IO)
    ;
        io.write_string(
            "ERROR: interpolated theorem e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
