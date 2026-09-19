:- module interpolated_theorem_egraph.

:- interface.

:- import_module io.
:- import_module symbolic_egraph.

:- func raw_semantic_law_count = int.
:- func nonreflexive_semantic_law_count = int.
:- func composite_semantic_law_count = int.
:- pred discovery_egraph(symbolic_egraph.egraph::out, io::di, io::uo) is det.
:- pred registry_gate is semidet.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module bool.
:- import_module learner_semantic_manifest.
:- import_module list.
:- import_module string.

:- func law_expr(string) = expr.
law_expr(Id) = app("semantic-law", [atom(Id)]).

:- func compose_expr(list(string)) = expr.
compose_expr([]) = atom("invalid-proof-compose").
compose_expr([Id]) = law_expr(Id).
compose_expr([A, B | Rest]) =
    compose_expr_acc(
        app("proof-compose", [law_expr(A), law_expr(B)]),
        Rest).

:- func compose_expr_acc(expr, list(string)) = expr.
compose_expr_acc(Acc, []) = Acc.
compose_expr_acc(Acc, [Id | Rest]) =
    compose_expr_acc(
        app("proof-compose", [Acc, law_expr(Id)]),
        Rest).

:- func right_compose_expr(list(string)) = expr.
right_compose_expr([]) = atom("invalid-proof-compose").
right_compose_expr([Id]) = law_expr(Id).
right_compose_expr([A, B | Rest]) =
    app("proof-compose", [
        law_expr(A),
        right_compose_expr([B | Rest])
    ]).

:- pred add_law(semantic_law::in,
    symbolic_egraph.egraph::in, symbolic_egraph.egraph::out) is det.
add_law(Law, E0, E) :-
    Id = law_id(Law),
    add_expr(law_expr(Id), E0, LawId, E1),
    (
        semantic_law.composite(Law) = yes
    ->
        Deps = semantic_law.dependencies(Law),
        Left = compose_expr(Deps),
        add_expr(Left, E1, ProofId, E2),
        merge(LawId, ProofId, E2, E3),
        (
            list.length(Deps) >= 3
        ->
            Right = right_compose_expr(Deps),
            add_expr(Right, E3, RightId, E4),
            merge(ProofId, RightId, E4, E)
        ;
            E = E3
        )
    ;
        (
            semantic_law.reflexive(Law) = yes
        ->
            add_expr(
                app("definitional-law", [law_expr(Id)]),
                E1, _, E)
        ;
            E = E1
        )
    ).

:- pred add_laws(list(semantic_law)::in,
    symbolic_egraph.egraph::in, symbolic_egraph.egraph::out) is det.
add_laws([], E, E).
add_laws([Law | Laws], E0, E) :-
    add_law(Law, E0, E1),
    add_laws(Laws, E1, E).

discovery_egraph(E, !IO) :-
    read_manifest(Laws, !IO),
    E0 = symbolic_egraph.empty,
    add_laws(Laws, E0, E).

main(!IO) :-
    discovery_egraph(EGraph, !IO),
    (
        class_count(EGraph) > 0,
        enode_count(EGraph) > 0
    ->
        io.write_string(
            "interpolated-theorem-egraph=pass "
            "source=learner-monolith "
            "symbolic-registry=absent "
            "refl-composition=disabled\\n",
            !IO)
    ;
        io.write_string(
            "ERROR: learner semantic e-graph is empty\\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
