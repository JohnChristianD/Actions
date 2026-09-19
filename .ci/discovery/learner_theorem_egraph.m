:- module learner_theorem_egraph.

:- interface.

:- import_module symbolic_egraph.
:- import_module list.
:- import_module string.

:- type theorem_transform
    ---> norm_replacement
    ;   clock_plus4.

:- type theorem_observable
    ---> count_step
    ;   qlog_step
    ;   endogenous_feedback
    ;   watkins_target.

:- type theorem_relation
    ---> invariant
    ;   iterate_invariant.

:- type theorem_term
    ---> theorem_term(theorem_transform, theorem_observable, theorem_relation).

:- type theorem_pattern
    ---> theorem_pattern(theorem_transform, theorem_observable).

:- type theorem_rewrite
    ---> theorem_rewrite(theorem_term, theorem_term).

:- func theorem_patterns = list(theorem_pattern).
:- func theorem_rewrites = list(theorem_rewrite).

:- func raw_terms = list(theorem_term).
:- func discovery_egraph = egraph.

:- pred quotient_terms(egraph::in, list(theorem_term)::in,
    list(theorem_term)::in, list(theorem_term)::out) is det.

:- func theorem_cost(theorem_term) = int.
:- pred extract_minimal(egraph::in, list(theorem_term)::in,
    list(theorem_term)::out) is det.

:- func candidate_name(theorem_term) = string.
:- func candidate_signature(theorem_term) = string.

:- pred prune_included(string::in, list(theorem_term)::in,
    list(theorem_term)::out) is det.

:- implementation.

theorem_patterns = [
    theorem_pattern(norm_replacement, count_step),
    theorem_pattern(norm_replacement, qlog_step),
    theorem_pattern(clock_plus4, endogenous_feedback),
    theorem_pattern(clock_plus4, watkins_target)
].

theorem_rewrites = [
    theorem_rewrite(
        theorem_term(norm_replacement, count_step, iterate_invariant),
        theorem_term(norm_replacement, count_step, invariant)),
    theorem_rewrite(
        theorem_term(norm_replacement, qlog_step, iterate_invariant),
        theorem_term(norm_replacement, qlog_step, invariant)),
    theorem_rewrite(
        theorem_term(clock_plus4, endogenous_feedback, iterate_invariant),
        theorem_term(clock_plus4, endogenous_feedback, invariant)),
    theorem_rewrite(
        theorem_term(clock_plus4, watkins_target, iterate_invariant),
        theorem_term(clock_plus4, watkins_target, invariant))
].

:- func pattern_terms(theorem_pattern) = list(theorem_term).
pattern_terms(theorem_pattern(T, O)) =
    [theorem_term(T, O, invariant),
     theorem_term(T, O, iterate_invariant)].

:- func expand_patterns(list(theorem_pattern)) = list(theorem_term).
expand_patterns([]) = [].
expand_patterns([P | Ps]) =
    pattern_terms(P) ++ expand_patterns(Ps).

raw_terms = expand_patterns(theorem_patterns).

:- func theorem_expr(theorem_term) = expr.
theorem_expr(theorem_term(T, O, R)) =
    app("learner-law", [
        atom(transform_symbol(T)),
        atom(observable_symbol(O)),
        atom(relation_symbol(R))
    ]).

:- func transform_symbol(theorem_transform) = string.
transform_symbol(norm_replacement) = "norm-replacement".
transform_symbol(clock_plus4) = "clock-plus4".

:- func observable_symbol(theorem_observable) = string.
observable_symbol(count_step) = "count-step".
observable_symbol(qlog_step) = "qlog-step".
observable_symbol(endogenous_feedback) = "endogenous-feedback".
observable_symbol(watkins_target) = "watkins-target".

:- func relation_symbol(theorem_relation) = string.
relation_symbol(invariant) = "invariant".
relation_symbol(iterate_invariant) = "iterate-invariant".

:- pred add_terms(list(theorem_term)::in, egraph::in,
    egraph::out) is det.
add_terms([], E, E).
add_terms([T | Ts], E0, E) :-
    add_expr(theorem_expr(T), E0, _, E1),
    add_terms(Ts, E1, E).

:- pred add_rewrites(list(theorem_rewrite)::in, egraph::in,
    egraph::out) is det.
add_rewrites([], E, E).
add_rewrites([theorem_rewrite(L, R) | Rs], E0, E) :-
    add_expr(theorem_expr(L), E0, LeftId, E1),
    add_expr(theorem_expr(R), E1, RightId, E2),
    merge(LeftId, RightId, E2, E3),
    add_rewrites(Rs, E3, E).

discovery_egraph = E :-
    E0 = symbolic_egraph.empty,
    add_terms(raw_terms, E0, E1),
    add_rewrites(theorem_rewrites, E1, E).

:- pred equivalent_to_prior(egraph::in, list(theorem_term)::in,
    theorem_term::in) is semidet.
equivalent_to_prior(_, [], _) :-
    fail.
equivalent_to_prior(E, [P | Ps], T) :-
    add_expr(theorem_expr(P), E, Pid, Ep),
    add_expr(theorem_expr(T), Ep, Tid, Et),
    ( if equivalent(Pid, Tid, Et) then
        true
    else
        equivalent_to_prior(E, Ps, T)
    ).

quotient_terms(_, [], _, []).
quotient_terms(E, [T | Ts], Prior, Out) :-
    ( if equivalent_to_prior(E, Prior, T) then
        quotient_terms(E, Ts, Prior, Out)
    else
        Out = [T | Rest],
        quotient_terms(E, Ts, [T | Prior], Rest)
    ).

theorem_cost(theorem_term(_, _, invariant)) = 1.
theorem_cost(theorem_term(_, _, iterate_invariant)) = 2.

:- pred insert_minimal(egraph::in, theorem_term::in,
    list(theorem_term)::in, list(theorem_term)::out) is det.
insert_minimal(_, T, [], [T]).
insert_minimal(E, T, [H | Hs], Out) :-
    ( if equivalent_to_prior(E, [H], T) then
        ( if theorem_cost(T) < theorem_cost(H) then
            Out = [T | Hs]
        else
            Out = [H | Hs]
        )
    else
        insert_minimal(E, T, Hs, Tail),
        Out = [H | Tail]
    ).

extract_minimal(_, [], []).
extract_minimal(E, [T | Ts], Out) :-
    extract_minimal(E, Ts, Rest),
    insert_minimal(E, T, Rest, Out).

candidate_name(theorem_term(norm_replacement, count_step, invariant)) =
    "candidate_normReplacement_countStep_invariant".
candidate_name(theorem_term(norm_replacement, qlog_step, invariant)) =
    "candidate_normReplacement_qLogStep_invariant".
candidate_name(theorem_term(clock_plus4, endogenous_feedback, invariant)) =
    "candidate_clockPlus4_endogenousFeedback_invariant".
candidate_name(theorem_term(clock_plus4, watkins_target, invariant)) =
    "candidate_clockPlus4_watkinsTarget_invariant".
candidate_name(theorem_term(_, _, iterate_invariant)) =
    "candidate_derived_iterate_form".

candidate_signature(theorem_term(norm_replacement, count_step, invariant)) =
    "canonicalCountStep K (C.replaceNorm s n)".
candidate_signature(theorem_term(norm_replacement, qlog_step, invariant)) =
    "canonicalQLogStep K (C.replaceNorm s n)".
candidate_signature(theorem_term(clock_plus4, endogenous_feedback, invariant)) =
    "canonicalEndogenousFeedback K (replaceClock s".
candidate_signature(theorem_term(clock_plus4, watkins_target, invariant)) =
    "canonicalWatkinsTarget K (replaceClock s".
candidate_signature(theorem_term(_, _, iterate_invariant)) =
    "iterate-derivation".

:- pred source_includes(string::in, theorem_term::in) is semidet.
source_includes(Source, Term) :-
    string.sub_string_search(Source, candidate_name(Term), _)
    ;
    string.sub_string_search(Source, candidate_signature(Term), _).

prune_included(_, [], []).
prune_included(Source, [T | Ts], Out) :-
    ( if source_includes(Source, T) then
        prune_included(Source, Ts, Out)
    else
        Out = [T | Rest],
        prune_included(Source, Ts, Rest)
    ).
