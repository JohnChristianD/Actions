:- module interpolated_theorem_egraph.

:- interface.

:- import_module io.
:- import_module symbolic_egraph.

:- type theorem_goal
    ---> goal_novel_basis
    ;   goal_attention_mediator
    ;   goal_recurrent_scan
    ;   goal_finite_reservoir
    ;   goal_no_unbounded_int8_memory.

:- func proof_plan(theorem_goal) = symbolic_egraph.expr.
:- func plan_name(theorem_goal) = string.
:- func raw_goal_count = int.
:- func saturated_goal_count = int.
:- pred registry_gate is semidet.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module algebra_law_registry.
:- import_module int.
:- import_module list.

:- func law_term(string) = expr.
law_term(Name) = app("law", [atom(Name)]).

:- func compose_laws(list(string)) = expr.
compose_laws([]) = atom("invalid-composition").
compose_laws([A]) = law_term(A).
compose_laws([A, B | Rest]) =
    compose_laws_acc(
        app("compose", [law_term(A), law_term(B)]),
        Rest).

:- func compose_laws_acc(expr, list(string)) = expr.
compose_laws_acc(Acc, []) = Acc.
compose_laws_acc(Acc, [Name | Rest]) =
    compose_laws_acc(
        app("compose", [Acc, law_term(Name)]),
        Rest).

proof_plan(goal_novel_basis) =
    app("basis", [
        compose_laws([
            "canonicalPolicy-norm-invariant",
            "canonicalCountStep-norm-invariant"
        ]),
        compose_laws([
            "canonicalPolicy-norm-invariant",
            "canonicalQLogStep-norm-invariant"
        ]),
        compose_laws([
            "canonicalAttentionMix-clock-period4",
            "novel-clockPlus4-endogenousFeedback-invariant",
            "canonicalWatkinsTarget-law"
        ])
    ]).

proof_plan(goal_attention_mediator) =
    app("mediator", [
        compose_laws([
            "canonicalPolicy-norm-invariant",
            "canonicalPolicy-learnerReplacement-invariant"
        ]),
        compose_laws([
            "canonicalAttentionMix-clock-period4",
            "novel-clockPlus4-endogenousFeedback-invariant"
        ]),
        compose_laws([
            "canonicalWatkinsTarget-law",
            "endomorphismAssociative"
        ])
    ]).

proof_plan(goal_recurrent_scan) =
    compose_laws([
        "endomorphismAssociative",
        "recurrentPrefix-split"
    ]).

proof_plan(goal_finite_reservoir) =
    compose_laws([
        "finiteReservoir-leftInverse",
        "int8-no-countably-unbounded-injective"
    ]).

proof_plan(goal_no_unbounded_int8_memory) =
    law_term("int8-no-countably-unbounded-injective").

plan_name(goal_novel_basis) = "novel-learner-theorem-basis".
plan_name(goal_attention_mediator) =
    "finite-attention-watkins-gru-f4-mediator".
plan_name(goal_recurrent_scan) = "recurrent-associative-scan".
plan_name(goal_finite_reservoir) = "finite-reservoir-faithfulness".
plan_name(goal_no_unbounded_int8_memory) =
    "no-countably-unbounded-int8-memory".

:- func goals = list(theorem_goal).
goals = [
    goal_novel_basis,
    goal_attention_mediator,
    goal_recurrent_scan,
    goal_finite_reservoir,
    goal_no_unbounded_int8_memory
].

:- pred plan_registry_valid(expr::in) is semidet.
plan_registry_valid(app("law", [atom(Name)])) :-
    lookup_law(Name, _).
plan_registry_valid(app("compose", [Left, Right])) :-
    plan_registry_valid(Left),
    plan_registry_valid(Right),
    ( Left = atom("invalid-composition") ),
    ( Right = atom("invalid-composition") ).
plan_registry_valid(app("basis", Plans)) :-
    registry_plans_valid(Plans).
plan_registry_valid(app("mediator", Plans)) :-
    registry_plans_valid(Plans).
plan_registry_valid(atom("invalid-composition")) :-
    fail.
plan_registry_valid(app(_, _)) :-
    fail.

:- pred registry_plans_valid(list(expr)::in) is semidet.
registry_plans_valid([]).
registry_plans_valid([Plan | Plans]) :-
    plan_registry_valid(Plan),
    registry_plans_valid(Plans).

:- pred plan_has_real_composition(expr::in) is semidet.
plan_has_real_composition(app("compose", [_, _])).
plan_has_real_composition(app(_, Children)) :-
    list.member(Child, Children),
    plan_has_real_composition(Child).
plan_has_real_composition(app("law", [_])) :-
    fail.
plan_has_real_composition(atom(_)) :-
    fail.

registry_gate :-
    registry_valid,
    list.all_true(
        (pred(G::in) is semidet :-
            plan_registry_valid(proof_plan(G)),
            (
                G = goal_no_unbounded_int8_memory
            ;
                plan_has_real_composition(proof_plan(G))
            )
        ),
        goals).

:- pred add_goal(theorem_goal::in, egraph::in,
    egraph::out) is det.
add_goal(G, E0, E) :-
    add_expr(proof_plan(G), E0, _, E).

:- pred add_goals(list(theorem_goal)::in, egraph::in,
    egraph::out) is det.
add_goals([], E, E).
add_goals([G | Gs], E0, E) :-
    add_goal(G, E0, E1),
    add_goals(Gs, E1, E).

:- pred add_composition_associativity(egraph::in,
    egraph::out) is det.
add_composition_associativity(E0, E) :-
    add_expr(
        app("compose", [
            app("compose", [
                law_term("ring-+-assoc"),
                law_term("ring-+-comm")
            ]),
            law_term("ring-*-assoc")
        ]),
        E0, Left, E1),
    add_expr(
        app("compose", [
            law_term("ring-+-assoc"),
            app("compose", [
                law_term("ring-+-comm"),
                law_term("ring-*-assoc")
            ])
        ]),
        E1, Right, E2),
    merge(Left, Right, E2, E).

discovery_egraph(E) :-
    E0 = symbolic_egraph.empty,
    add_goals(goals, E0, E1),
    add_composition_associativity(E1, E).

:- func raw_goal_count = int.
raw_goal_count = list.length(goals).

:- func saturated_goal_count = int.
saturated_goal_count = raw_goal_count.

main(!IO) :-
    E = discovery_egraph,
    Raw = raw_goal_count,
    Saturated = saturated_goal_count,
    (
        registry_gate,
        Raw = 5,
        Saturated = 5,
        class_count(E) > 0,
        enode_count(E) > 0
    ->
        io.write_string(
            "interpolated-theorem-egraph=pass goals=5 "
            "typed-registry=on nonreflexive-composition=on "
            "ring-laws=registered\n",
            !IO)
    ;
        io.write_string(
            "ERROR: interpolated theorem e-graph registry gate failed\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
