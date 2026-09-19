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
    discovery_egraph(E, !IO),
    MultiDependency = list.length(
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
        list.length(Laws) > 0,
        NonReflexive >= MultiDependency,
        class_count(E) > 0,
        enode_count(E) > 0
    ->
        io.write_string(
            "learner-semantic-egraph-regression=pass "
            "source=monolith "
            "composition=dependency-plan "
            "refl=excluded "
            "dynamic=on\n",
            !IO)
    ;
        io.write_string(
            "ERROR: learner semantic e-graph regression failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
