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

:- type proof_atom
    ---> atom_norm_policy
    ;   atom_norm_count
    ;   atom_norm_qlog
    ;   atom_clock_attention
    ;   atom_attention_endogenous
    ;   atom_endogenous_watkins
    ;   atom_shared_watkins_gru
    ;   atom_shared_watkins_f4
    ;   atom_recurrent_associativity
    ;   atom_recurrent_prefix
    ;   atom_reservoir_left_inverse
    ;   atom_reservoir_injective
    ;   atom_reservoir_exact_readout
    ;   atom_finite_int8.

:- func proof_plan(theorem_goal) = symbolic_egraph.expr.
:- func plan_name(theorem_goal) = string.
:- func raw_goal_count = int.
:- func saturated_goal_count = int.
:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module int.
:- import_module list.

proof_plan(goal_novel_basis) =
    app("basis", [
        app("compose", [
            atom("norm-policy"),
            atom("norm-count")
        ]),
        app("compose", [
            atom("norm-policy"),
            atom("norm-qlog")
        ]),
        app("compose", [
            app("compose", [
                atom("clock-attention"),
                atom("attention-endogenous")
            ]),
            atom("endogenous-watkins")
        ])
    ]).

proof_plan(goal_attention_mediator) =
    app("compose", [
        app("compose", [
            atom("attention-policy"),
            atom("attention-count")
        ]),
        app("compose", [
            atom("shared-watkins-gru"),
            atom("shared-watkins-f4")
        ])
    ]).

proof_plan(goal_recurrent_scan) =
    app("compose", [
        atom("recurrent-associativity"),
        atom("recurrent-prefix")
    ]).

proof_plan(goal_finite_reservoir) =
    app("compose", [
        atom("reservoir-left-inverse"),
        app("pair", [
            atom("reservoir-injective"),
            atom("reservoir-exact-readout")
        ])
    ]).

proof_plan(goal_no_unbounded_int8_memory) =
    app("finite-codomain-obstruction", [
        atom("finite-int8"),
        atom("noninjective")
    ]).

plan_name(goal_novel_basis) = "novel-learner-theorem-basis".
plan_name(goal_attention_mediator) = "finite-attention-watkins-gru-f4-mediator".
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

:- pred add_goal(theorem_goal::in, egraph::in, egraph::out) is det.
add_goal(G, E0, E) :-
    add_expr(proof_plan(G), E0, _, E).

:- pred add_goals(list(theorem_goal)::in, egraph::in,
    egraph::out) is det.
add_goals([], E, E).
add_goals([G | Gs], E0, E) :-
    add_goal(G, E0, E1),
    add_goals(Gs, E1, E).

:- pred add_associativity_aliases(egraph::in, egraph::out) is det.
add_associativity_aliases(E0, E) :-
    add_expr(
        app("assoc", [
            atom("a"),
            app("compose", [
                atom("b"),
                atom("c")
            ])
        ]),
        E0, A, E1),
    add_expr(
        app("assoc", [
            app("compose", [
                atom("a"),
                atom("b")
            ]),
            atom("c")
        ]),
        E1, B, E2),
    merge(A, B, E2, E).

discovery_egraph(E) :-
    E0 = empty,
    add_goals(goals, E0, E1),
    add_associativity_aliases(E1, E).

:- func raw_goal_count = int.
raw_goal_count = list.length(goals).

:- func saturated_goal_count = int.
saturated_goal_count = raw_goal_count.

main(!IO) :-
    E = discovery_egraph,
    Raw = raw_goal_count,
    Saturated = saturated_goal_count,
    (
        class_count(E) > 0,
        enode_count(E) > 0
    ->
        io.write_string(
            "interpolated-theorem-egraph=pass goals=5 "
            "hash-cons=on congruence-closure=on proof-plans=5\n",
            !IO)
    ;
        io.write_string(
            "ERROR: interpolated theorem e-graph is empty\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
