:- module interpolated_theorem_egraph.

:- interface.

:- import_module io.
:- import_module list.
:- import_module symbolic_egraph.
:- import_module learner_semantic_extractor.

:- pred discovery_egraph(
    symbolic_egraph.egraph::out,
    int::out,
    io::di, io::uo) is det.
:- pred discovery_egraph_from_laws(
    list(semantic_law)::in,
    symbolic_egraph.egraph::out,
    int::out) is det.
:- func semantic_rewrite_rules = list(rewrite_rule).
  :- func graph_plan_expr(list(string)) = expr.
:- func law_expr(string) = expr.

:- implementation.

:- import_module int.

graph_plan_expr(Ids) =
    app("graph-discovered-proof-plan", [left_assoc_expr(Ids)]).

semantic_rewrite_rules = [
    rewrite_rule(
        "proof-compose-associativity",
        papp("proof-compose", [
            pvar("A"),
            papp("proof-compose", [pvar("B"), pvar("C")])
        ]),
        papp("proof-compose", [
            papp("proof-compose", [pvar("A"), pvar("B")]),
            pvar("C")
        ])),
    rewrite_rule(
        "proof-compose-empty-right",
        papp("proof-compose", [
            pvar("A"),
            papp("empty-proof-compose", [])
        ]),
        pvar("A")),
    rewrite_rule(
        "proof-compose-empty-left",
        papp("proof-compose", [
            papp("empty-proof-compose", []),
            pvar("A")
        ]),
        pvar("A"))
].

law_expr(Id) = app("semantic-law", [atom(Id)]).

:- func left_assoc_expr(list(string)) = expr.
left_assoc_expr([]) = atom("empty-proof-compose").
left_assoc_expr([Id]) = law_expr(Id).
left_assoc_expr([A, B | Rest]) =
    left_assoc_expr_acc(
        app("proof-compose", [law_expr(A), law_expr(B)]),
        Rest).

:- func left_assoc_expr_acc(expr, list(string)) = expr.
left_assoc_expr_acc(Acc, []) = Acc.
left_assoc_expr_acc(Acc, [Id | Rest]) =
    left_assoc_expr_acc(
        app("proof-compose", [Acc, law_expr(Id)]),
        Rest).

:- func right_assoc_expr(list(string)) = expr.
right_assoc_expr([]) = atom("empty-proof-compose").
right_assoc_expr([Id]) = law_expr(Id).
right_assoc_expr([A, B | Rest]) =
    app("proof-compose", [
        law_expr(A),
        right_assoc_expr([B | Rest])
    ]).

:- pred add_law(
    semantic_law::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out,
    int::in, int::out) is det.
add_law(Law, E0, E, Quotient0, Quotient) :-
    Id = law_id(Law),
    add_expr(law_expr(Id), E0, _, E1),
    (
        is_composite(Law)
    ->
        Deps = law_dependencies(Law),
        Left = left_assoc_expr(Deps),
        add_expr(
            app("derived-proof-plan", [
                law_expr(Id),
                Left
            ]),
            E1, _, E2),
        (
            list.length(Deps) >= 3
        ->
            Right = right_assoc_expr(Deps),
            add_expr(
                app("derived-proof-plan", [
                    law_expr(Id),
                    Right
                ]),
                E2, RightClass, E3),
            add_expr(
                app("derived-proof-plan", [
                    law_expr(Id),
                    Left
                ]),
                E3, LeftClass, E4),
            merge(LeftClass, RightClass, E4, E),
            Quotient = Quotient0 + 1
        ;
            E = E2,
            Quotient = Quotient0
        )
    ;
        (
            is_reflexive(Law)
        ->
            add_expr(
                app("definitional-law", [law_expr(Id)]),
                E1, _, E)
        ;
            E = E1
        ),
        Quotient = Quotient0
    ).

:- pred add_laws(
    list(semantic_law)::in,
    symbolic_egraph.egraph::in,
    symbolic_egraph.egraph::out,
    int::in, int::out) is det.
add_laws([], E, E, Count, Count).
add_laws([Law | Laws], E0, E, Count0, Count) :-
    add_law(Law, E0, E1, Count0, Count1),
    add_laws(Laws, E1, E, Count1, Count).

discovery_egraph_from_laws(Laws, E, QuotientCount) :-
    E0 = symbolic_egraph.empty,
    add_laws(Laws, E0, E, 0, QuotientCount).

discovery_egraph(E, QuotientCount, !IO) :-
    read_semantic_laws(Laws, !IO),
    discovery_egraph_from_laws(Laws, E, QuotientCount).
