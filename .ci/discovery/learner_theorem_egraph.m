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

:- func raw_terms = list(theorem_term).
:- func discovery_egraph = eqvclass.eqvclass(theorem_term).

:- pred quotient_terms(eqvclass.eqvclass(theorem_term)::in,
    list(theorem_term)::in, list(theorem_term)::in,
    list(theorem_term)::out) is det.

:- func candidate_name(theorem_term) = string.
:- func candidate_signature(theorem_term) = string.

:- pred prune_included(string::in, list(theorem_term)::in,
    list(theorem_term)::out) is det.

:- implementation.

:- func transforms = list(theorem_transform).
transforms = [norm_replacement, clock_plus4].

:- func observables = list(theorem_observable).
observables = [count_step, qlog_step, endogenous_feedback, watkins_target].

:- func relations = list(theorem_relation).
relations = [invariant, iterate_invariant].

:- pred admissible(theorem_transform::in, theorem_observable::in) is semidet.
admissible(norm_replacement, count_step).
admissible(norm_replacement, qlog_step).
admissible(clock_plus4, endogenous_feedback).
admissible(clock_plus4, watkins_target).

:- func raw_terms = list(theorem_term).
raw_terms = build_raw(transforms, observables).

:- func build_raw(list(theorem_transform), list(theorem_observable))
    = list(theorem_term).
build_raw([], _) = [].
build_raw([T | Ts], Os) =
    admissible_terms(T, Os) ++ build_raw(Ts, Os).

:- func admissible_terms(theorem_transform, list(theorem_observable))
    = list(theorem_term).
admissible_terms(_, []) = [].
admissible_terms(T, [O | Os]) =
    ( if admissible(T, O) then
        relation_terms(T, O, relations) ++ admissible_terms(T, Os)
    else
        admissible_terms(T, Os)
    ).

:- func relation_terms(theorem_transform, theorem_observable,
    list(theorem_relation)) = list(theorem_term).
relation_terms(_, _, []) = [].
relation_terms(T, O, [R | Rs]) =
    [theorem_term(T, O, R) | relation_terms(T, O, Rs)].

:- func canonical_term(theorem_term) = theorem_term.
canonical_term(theorem_term(T, O, _)) =
    theorem_term(T, O, invariant).

:- pred build_egraph(list(theorem_term)::in,
    eqvclass.eqvclass(theorem_term)::in,
    eqvclass.eqvclass(theorem_term)::out) is det.
build_egraph([], E, E).
build_egraph([T | Ts], E0, E) :-
    C = canonical_term(T),
    ( if T = C then
        E1 = E0
    else
        E1 = eqvclass.ensure_equivalence(E0, T, C)
    ),
    build_egraph(Ts, E1, E).

discovery_egraph = E :-
    build_egraph(raw_terms, eqvclass.init, E).

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
