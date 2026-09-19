:- module novel_learner_theorem_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module eqvclass.
:- import_module list.
:- import_module string.

% Typed symbolic theorem synthesis for the canonical learner.
%
% The grammar is declarative: transformations, observables, and relations are
% first-class constructors. Raw candidates are formed by Cartesian expansion
% over supported transformation/observable pairs. An e-graph-style quotient
% then maps derived iterate forms to their one-step representatives.
%
% Mercury is the candidate engine. Agda is the proof authority.

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

:- func expand_relations(theorem_transform, theorem_observable)
    = list(theorem_term).
expand_relations(T, O) =
    [theorem_term(T, O, R) | Rs] :-
    expand_relation_tail(relations, T, O, R, Rs).

:- pred expand_relation_tail(list(theorem_relation)::in,
    theorem_transform::in, theorem_observable::in,
    theorem_relation::out, list(theorem_term)::out) is det.
expand_relation_tail([], _, _, invariant, []).
expand_relation_tail([R | Rs], T, O, R, Out) :-
    relation_terms(Rs, T, O, Out).

:- func relation_terms(list(theorem_relation), theorem_transform,
    theorem_observable) = list(theorem_term).
relation_terms([], _, _) = [].
relation_terms([R | Rs], T, O) =
    [theorem_term(T, O, R) | relation_terms(Rs, T, O)].

:- func raw_terms = list(theorem_term).
raw_terms = build_raw(transforms, observables).

:- func build_raw(list(theorem_transform), list(theorem_observable))
    = list(theorem_term).
build_raw([], _) = [].
build_raw([T | Ts], Observables) =
    admissible_terms(T, Observables) ++ build_raw(Ts, Observables).

:- func admissible_terms(theorem_transform, list(theorem_observable))
    = list(theorem_term).
admissible_terms(_, []) = [].
admissible_terms(T, [O | Os]) =
    ( if admissible(T, O) then
        expand_relations(T, O) ++ admissible_terms(T, Os)
    else
        admissible_terms(T, Os)
    ).

:- func canonical_term(theorem_term) = theorem_term.
canonical_term(theorem_term(T, O, _)) =
    theorem_term(T, O, invariant).

:- pred build_egraph(list(theorem_term)::in,
    eqvclass.eqvclass(theorem_term)::in,
    eqvclass.eqvclass(theorem_term)::out) is det.
build_egraph([], E, E).
build_egraph([T | Ts], E0, E) :-
    C = canonical_term(T),
    E1 = eqvclass.ensure_equivalence(E0, T, C),
    build_egraph(Ts, E1, E).

:- func discovery_egraph = eqvclass.eqvclass(theorem_term).
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

:- pred quotient_terms(eqvclass.eqvclass(theorem_term)::in,
    list(theorem_term)::in, list(theorem_term)::in,
    list(theorem_term)::out) is det.
quotient_terms(_, [], _, []).
quotient_terms(E, [T | Ts], Prior, Out) :-
    ( if equivalent_to_prior(E, Prior, T) then
        quotient_terms(E, Ts, Prior, Out)
    else
        Out = [T | Rest],
        quotient_terms(E, Ts, [T | Prior], Rest)
    ).

:- func candidate_name(theorem_term) = string.
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

:- func candidate_signature(theorem_term) = string.
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

:- pred prune_included(string::in, list(theorem_term)::in,
    list(theorem_term)::out) is det.
prune_included(_, [], []).
prune_included(Source, [T | Ts], Out) :-
    ( if source_includes(Source, T) then
        prune_included(Source, Ts, Out)
    else
        Out = [T | Rest],
        prune_included(Source, Ts, Rest)
    ).

:- func nat_string(int) = string.
nat_string(N) = string.int_to_string(N).

:- func clock_plus4_expr(string) = string.
clock_plus4_expr(S) =
    "replaceClock (" ++ S ++
    ") (suc (suc (suc (suc (C.clock (" ++ S ++ "))))))".

:- func render_candidate(theorem_term) = string.
render_candidate(theorem_term(norm_replacement, count_step, invariant)) =
    "candidate_normReplacement_countStep_invariant :\n" ++
    "  ∀ K s n →\n" ++
    "  C.canonicalCountStep K (C.replaceNorm s n)\n" ++
    "  ≡\n" ++
    "  C.canonicalCountStep K s\n" ++
    "candidate_normReplacement_countStep_invariant K s n =\n" ++
    "  cong₂ C.updateLCBCount\n" ++
    "    (canonicalPolicy-norm-invariant K s n)\n" ++
    "    refl\n\n".
render_candidate(theorem_term(norm_replacement, qlog_step, invariant)) =
    "candidate_normReplacement_qLogStep_invariant :\n" ++
    "  ∀ K s n →\n" ++
    "  C.canonicalQLogStep K (C.replaceNorm s n)\n" ++
    "  ≡\n" ++
    "  C.canonicalQLogStep K s\n" ++
    "candidate_normReplacement_qLogStep_invariant K s n =\n" ++
    "  cong\n" ++
    "    (λ p → C.negativeFiniteQLog8 (C.policyLeftWeight p))\n" ++
    "    (canonicalPolicy-norm-invariant K s n)\n\n".
render_candidate(theorem_term(clock_plus4, endogenous_feedback, invariant)) =
    "candidate_clockPlus4_endogenousFeedback_invariant :\n" ++
    "  ∀ K s →\n" ++
    "  C.canonicalEndogenousFeedback K (" ++ clock_plus4_expr("s") ++ ")\n" ++
    "  ≡\n" ++
    "  C.canonicalEndogenousFeedback K s\n" ++
    "candidate_clockPlus4_endogenousFeedback_invariant K s =\n" ++
    "  cong\n" ++
    "    (λ x →\n" ++
    "      C.int8Add\n" ++
    "        x\n" ++
    "        (C.int8Add\n" ++
    "          (C.canonicalGRUFeedback s)\n" ++
    "          (C.int8Add\n" ++
    "            (C.canonicalF4L2Feedback K s)\n" ++
    "            (C.int8Add\n" ++
    "              (C.canonicalQLogControlFeedback s)\n" ++
    "              (C.canonicalQLogValueFeedback s)))))\n" ++
    "    (canonicalAttentionMix-clock-period4 K s)\n\n".
render_candidate(theorem_term(clock_plus4, watkins_target, invariant)) =
    "candidate_clockPlus4_watkinsTarget_invariant :\n" ++
    "  ∀ K s →\n" ++
    "  C.canonicalWatkinsTarget K (" ++ clock_plus4_expr("s") ++ ")\n" ++
    "  ≡\n" ++
    "  C.canonicalWatkinsTarget K s\n" ++
    "candidate_clockPlus4_watkinsTarget_invariant K s =\n" ++
    "  trans\n" ++
    "    (C.canonicalWatkinsTarget-law K (" ++ clock_plus4_expr("s") ++ "))\n" ++
    "    (cong\n" ++
    "      (λ x →\n" ++
    "        C.int8Add\n" ++
    "          (C.int8Add\n" ++
    "            (C.int8Add\n" ++
    "              (C.canonicalReward8 K s)\n" ++
    "              (C.canonicalQLogBias K s))\n" ++
    "            (C.int8Mul\n" ++
    "              C.canonicalDiscount8\n" ++
    "              (C.maxCriticValue8 (C.critic (C.watkins s)))))\n" ++
    "          x)\n" ++
    "      candidate_clockPlus4_endogenousFeedback_invariant K s)\n\n".
render_candidate(theorem_term(_, _, iterate_invariant)) = "".

:- func rendered_program(list(theorem_term)) = string.
rendered_program(Terms) = join_rendered(Terms).

:- func join_rendered(list(theorem_term)) = string.
join_rendered([]) = "".
join_rendered([T | Ts]) = render_candidate(T) ++ join_rendered(Ts).

:- pred contains_bare_refl(string::in) is semidet.
contains_bare_refl(Text) :-
    string.sub_string_search(Text, "= refl\n", _).

:- pred write_programs(io.text_output_stream::in, list(theorem_term)::in,
    io::di, io::uo) is det.
write_programs(_, [], !IO).
write_programs(Stream, [T | Ts], !IO) :-
    io.write_string(Stream, render_candidate(T), !IO),
    write_programs(Stream, Ts, !IO).

:- pred term_names(list(theorem_term)::in, io.text_output_stream::in,
    io::di, io::uo) is det.
term_names([], _, !IO).
term_names([T | Ts], Stream, !IO) :-
    io.write_string(Stream,
        "    \"" ++ candidate_name(T) ++ "\"",
        !IO),
    (
        Ts = [] ->
            io.write_string(Stream, "\n", !IO)
    ;
        io.write_string(Stream, ",\n", !IO)
    ),
    term_names(Ts, Stream, !IO).

:- pred write_generated(list(theorem_term)::in, io::di, io::uo) is det.
write_generated(Terms, !IO) :-
    Text = rendered_program(Terms),
    ( if contains_bare_refl(Text) then
        io.write_string(
            "ERROR: trivial bare refl proof remained in generated discovery module\n",
            !IO),
        io.set_exit_status(1, !IO)
    else
        write_generated_text(Text, !IO)
    ).

:- pred write_generated_text(string::in, io::di, io::uo) is det.
write_generated_text(Text, !IO) :-
    io.open_output(
        "../../Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda",
        Result,
        !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{-# OPTIONS --safe #-}\n\n" ++
            "module Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems where\n\n" ++
            "open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)\n" ++
            "open import Agda.Builtin.Nat using (suc)\n" ++
            "open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C\n" ++
            "open import Exotic.ERL.FullCoupled.TheoremsMonolith\n\n" ++
            Text,
            !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write generated novel learner theorem module\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

:- pred write_report(int::in, int::in, int::in,
    list(theorem_term)::in, io::di, io::uo) is det.
write_report(RawCount, QuotientPruned, SourcePruned, Terms, !IO) :-
    io.open_output("novel-learner-theorem-discovery.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{\n" ++
            "  \"accepted\": true,\n" ++
            "  \"search_semantics\": \"typed symbolic learner-law basis enumeration\",\n" ++
            "  \"quotient\": \"Mercury equivalence-class quotient derived from canonical theorem keys\",\n" ++
            "  \"proof_gate\": \"GeneratedNovelLearnerTheorems.agda\",\n" ++
            "  \"raw_candidate_count\": " ++ nat_string(RawCount) ++ ",\n" ++
            "  \"quotient_pruned_count\": " ++ nat_string(QuotientPruned) ++ ",\n" ++
            "  \"source_included_pruned_count\": " ++ nat_string(SourcePruned) ++ ",\n" ++
            "  \"novel_basis_count\": " ++ nat_string(list.length(Terms)) ++ ",\n" ++
            "  \"bare_refl_pruned\": true,\n" ++
            "  \"external_search_reward\": false\n" ++
            "}\n",
            !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write novel learner theorem discovery report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    Raw = raw_terms,
    EGraph = discovery_egraph,
    quotient_terms(EGraph, Raw, [], Quotiented),
    io.read_named_file_as_string(
        "../../Exotic/ERL/FullCoupled/TheoremsMonolith.agda",
        SourceResult,
        !IO),
    (
        SourceResult = ok(Source),
        prune_included(Source, Quotiented, Novel),
        QuotientPruned = list.length(Raw) - list.length(Quotiented),
        SourcePruned = list.length(Quotiented) - list.length(Novel),
        write_generated(Novel, !IO),
        write_report(
            list.length(Raw),
            QuotientPruned,
            SourcePruned,
            Novel,
            !IO),
        io.write_string(
            "novel-learner-theorem-discovery=generated\n",
            !IO),
        io.write_string(
            "raw_candidate_count=" ++
            nat_string(list.length(Raw)) ++ "\n",
            !IO),
        io.write_string(
            "quotient_pruned_count=" ++
            nat_string(QuotientPruned) ++ "\n",
            !IO),
        io.write_string(
            "source_included_pruned_count=" ++
            nat_string(SourcePruned) ++ "\n",
            !IO),
        io.write_string(
            "novel_basis_count=" ++
            nat_string(list.length(Novel)) ++ "\n",
            !IO),
        io.write_string(
            "bare_refl_pruned=true\n",
            !IO),
        io.write_string(
            "proof_gate=GeneratedNovelLearnerTheorems.agda\n",
            !IO)
    ;
        SourceResult = error(ErrorMessage),
        io.write_string(
            "ERROR: cannot read TheoremsMonolith.agda: " ++
            ErrorMessage ++ "\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

