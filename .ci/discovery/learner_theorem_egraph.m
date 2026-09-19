:- module learner_theorem_egraph.

:- interface.

:- import_module eqvclass.
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
    ---> normalize_iterate.

:- func theorem_patterns = list(theorem_pattern).
:- func theorem_rewrites = list(theorem_rewrite).

:- func raw_terms = list(theorem_term).
:- func discovery_egraph = eqvclass.eqvclass(theorem_term).

:- pred saturate(
    eqvclass.eqvclass(theorem_term)::in,
    list(theorem_rewrite)::in,
    list(theorem_term)::in,
    eqvclass.eqvclass(theorem_term)::out) is det.

:- pred quotient_terms(eqvclass.eqvclass(theorem_term)::in,
    list(theorem_term)::in, list(theorem_term)::in,
    list(theorem_term)::out) is det.

:- func theorem_cost(theorem_term) = int.
:- pred extract_minimal(eqvclass.eqvclass(theorem_term)::in,
    list(theorem_term)::in, list(theorem_term)::out) is det.

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

theorem_rewrites = [normalize_iterate].

:- func pattern_terms(theorem_pattern) = list(theorem_term).
pattern_terms(theorem_pattern(T, O)) =
    [theorem_term(T, O, invariant), theorem_term(T, O, iterate_invariant)].

:- func raw_terms = list(theorem_term).
raw_terms = expand_patterns(theorem_patterns).

:- func expand_patterns(list(theorem_pattern)) = list(theorem_term).
expand_patterns([]) = [].
expand_patterns([P | Ps]) = pattern_terms(P) ++ expand_patterns(Ps).

:- func rewrite_once(theorem_rewrite, theorem_term) = theorem_term.
rewrite_once(normalize_iterate, theorem_term(T, O, iterate_invariant)) =
    theorem_term(T, O, invariant).
rewrite_once(normalize_iterate, T) = T.

:- pred add_rewrite(
    eqvclass.eqvclass(theorem_term)::in,
    theorem_rewrite::in,
    theorem_term::in,
    eqvclass.eqvclass(theorem_term)::out) is det.
add_rewrite(E0, Rule, T, E) :-
    R = rewrite_once(Rule, T),
    ( if T = R then
        E = E0
    else
        E = eqvclass.ensure_equivalence(E0, T, R)
    ).

:- pred add_rewrites(
    eqvclass.eqvclass(theorem_term)::in,
    list(theorem_rewrite)::in,
    theorem_term::in,
    eqvclass.eqvclass(theorem_term)::out) is det.
add_rewrites(E, [], _, E).
add_rewrites(E0, [Rule | Rules], T, E) :-
    add_rewrite(E0, Rule, T, E1),
    add_rewrites(E1, Rules, T, E).

:- pred saturate_terms(
    eqvclass.eqvclass(theorem_term)::in,
    list(theorem_rewrite)::in,
    list(theorem_term)::in,
    eqvclass.eqvclass(theorem_term)::out) is det.
saturate_terms(E, _, [], E).
saturate_terms(E0, Rules, [T | Ts], E) :-
    add_rewrites(E0, Rules, T, E1),
    saturate_terms(E1, Rules, Ts, E).

saturate(E0, Rules, Terms, E) :-
    saturate_terms(E0, Rules, Terms, E).

discovery_egraph = E :-
    E0 = eqvclass.init,
    saturate(E0, theorem_rewrites, raw_terms, E).

:- pred equivalent_to_prior(eqvclass.eqvclass(theorem_term)::in,
    list(theorem_term)::in, theorem_term::in) is semidet.
equivalent_to_prior(_, [], _) :-
    fail.
equivalent_to_prior(E, [P | Ps], T) :-
    ( if eqvclass.same_eqvclass(E, P, T) then
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

:- pred insert_minimal(eqvclass.eqvclass(theorem_term)::in,
    theorem_term::in, list(theorem_term)::in, list(theorem_term)::out) is det.
insert_minimal(E, T, [], [T]).
insert_minimal(E, T, [H | Hs], Out) :-
    ( if eqvclass.same_eqvclass(E, T, H) then
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
