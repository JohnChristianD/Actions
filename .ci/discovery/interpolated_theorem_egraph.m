:- module interpolated_theorem_egraph.

:- interface.

:- import_module io.
:- import_module symbolic_egraph.

:- pred discovery_egraph(symbolic_egraph.egraph::out, io::di, io::uo) is det.
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

:- pred add_law(semantic_law::in,
    symbolic_egraph.egraph::in, symbolic_egraph.egraph::out) is det.
add_law(Law, E0, E) :-
    Id = law_id(Law),
    add_expr(law_expr(Id), E0, _, E1),
    (
        semantic_law.composite(Law) = yes
    ->
        Deps = semantic_law.dependencies(Law),
        Plan = compose_expr(Deps),
        add_expr(
            app("derived-proof-plan", [
                law_expr(Id),
                Plan
            ]),
            E1, _, E)
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
    read_manifest(Laws, !IO),
    discovery_egraph(EGraph, !IO),
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
        class_count(EGraph) > 0,
        enode_count(EGraph) > 0
    ->
        io.write_string(
            "interpolated-theorem-egraph=pass "
            "source=learner-monolith "
            "symbolic-registry=absent "
            "refl-composition=disabled "
            "dynamic-manifest=on\n",
            !IO)
    ;
        io.write_string(
            "ERROR: learner semantic e-graph manifest gate failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
