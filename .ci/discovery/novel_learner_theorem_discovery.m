:- module novel_learner_theorem_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module eqvclass.
:- import_module list.
:- import_module string.

% ---------------------------------------------------------------------------
% Novel learner-theorem grammar.
%
% The discovery target is no longer a TSTS/search theorem. It is the basis
% of genuinely new learner laws that are not already represented in the
% canonical theorem monolith.
%
% The raw grammar includes iterate-equivariance consequences. The small
% equivalence-class quotient identifies those as consequences of the stronger
% full-step equivariance law and emits only the minimal representative.
% ---------------------------------------------------------------------------

:- type theorem_relation
    ---> target_invariant
    ;   full_step_equivariant
    ;   iterate_equivariant.

:- type theorem_transform
    ---> norm_replacement
    ;   clock_plus4.

:- type theorem_term
    ---> theorem_term(theorem_relation, theorem_transform).

:- func raw_terms = list(theorem_term).
raw_terms =
    [ theorem_term(target_invariant, norm_replacement)
    , theorem_term(target_invariant, clock_plus4)
    , theorem_term(full_step_equivariant, norm_replacement)
    , theorem_term(full_step_equivariant, clock_plus4)
    , theorem_term(iterate_equivariant, norm_replacement)
    , theorem_term(iterate_equivariant, clock_plus4)
    ].

% Iterate equivariance is a direct consequence schema of full-step
% equivariance. The equivalence-class quotient therefore collapses the
% iterate candidate into the corresponding full-step candidate before
% anything reaches the Agda proof gate.

:- func discovery_egraph =
    eqvclass.eqvclass(theorem_term).
discovery_egraph = E4 :-
    E0 = eqvclass.init,
    E1 = eqvclass.ensure_equivalence(
        E0,
        theorem_term(full_step_equivariant, norm_replacement),
        theorem_term(iterate_equivariant, norm_replacement)),
    E2 = eqvclass.ensure_equivalence(
        E1,
        theorem_term(full_step_equivariant, clock_plus4),
        theorem_term(iterate_equivariant, clock_plus4)),
    E2 = E4.

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
candidate_name(theorem_term(target_invariant, norm_replacement)) =
    "candidate_watkins_target_norm_invariant".
candidate_name(theorem_term(target_invariant, clock_plus4)) =
    "candidate_watkins_target_clock_plus4_invariant".
candidate_name(theorem_term(full_step_equivariant, norm_replacement)) =
    "candidate_full_step_norm_replacement_equivariant".
candidate_name(theorem_term(full_step_equivariant, clock_plus4)) =
    "candidate_full_step_clock_plus4_equivariant".
candidate_name(theorem_term(iterate_equivariant, norm_replacement)) =
    "candidate_iterate_norm_replacement_equivariant".
candidate_name(theorem_term(iterate_equivariant, clock_plus4)) =
    "candidate_iterate_clock_plus4_equivariant".

:- pred source_includes(string::in, theorem_term::in) is semidet.
source_includes(Source, Term) :-
    string.sub_string_search(Source, candidate_name(Term), _).

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
render_candidate(theorem_term(target_invariant, norm_replacement)) =
    "candidate_watkins_target_norm_invariant :\n" ++
    "  ∀ K s n →\n" ++
    "  C.canonicalWatkinsTarget K (replaceNorm s n)\n" ++
    "  ≡\n" ++
    "  C.canonicalWatkinsTarget K s\n" ++
    "candidate_watkins_target_norm_invariant K s n = refl\n\n".
render_candidate(theorem_term(target_invariant, clock_plus4)) =
    "candidate_watkins_target_clock_plus4_invariant :\n" ++
    "  ∀ K s →\n" ++
    "  C.canonicalWatkinsTarget K (" ++ clock_plus4_expr("s") ++ ")\n" ++
    "  ≡\n" ++
    "  C.canonicalWatkinsTarget K s\n" ++
    "candidate_watkins_target_clock_plus4_invariant K s = refl\n\n".
render_candidate(theorem_term(full_step_equivariant, norm_replacement)) =
    "candidate_full_step_norm_replacement_equivariant :\n" ++
    "  ∀ K s n →\n" ++
    "  C.canonicalFullStep K (replaceNorm s n)\n" ++
    "  ≡\n" ++
    "  replaceNorm (C.canonicalFullStep K s) n\n" ++
    "candidate_full_step_norm_replacement_equivariant K s n = refl\n\n".
render_candidate(theorem_term(full_step_equivariant, clock_plus4)) =
    "candidate_full_step_clock_plus4_equivariant :\n" ++
    "  ∀ K s →\n" ++
    "  C.canonicalFullStep K (" ++ clock_plus4_expr("s") ++ ")\n" ++
    "  ≡\n" ++
    "  " ++ clock_plus4_expr("C.canonicalFullStep K s") ++ "\n" ++
    "candidate_full_step_clock_plus4_equivariant K s = refl\n\n".
render_candidate(theorem_term(iterate_equivariant, _)) = "".

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
    io.open_output(
        "../../Exotic/ERL/FullCoupled/GeneratedNovelLearnerTheorems.agda",
        Result,
        !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{-# OPTIONS --safe #-}\n\n" ++
            "module Exotic.ERL.FullCoupled.GeneratedNovelLearnerTheorems where\n\n" ++
            "open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C\n" ++
            "open import Exotic.ERL.FullCoupled.TheoremsMonolith\n\n",
            !IO),
        write_programs(Stream, Terms, !IO),
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
            "  \"quotient\": \"Mercury equivalence-class quotient; iterate equivariance is derived from full-step equivariance\",\n" ++
            "  \"proof_gate\": \"GeneratedNovelLearnerTheorems.agda\",\n" ++
            "  \"raw_candidate_count\": " ++ nat_string(RawCount) ++ ",\n" ++
            "  \"quotient_pruned_count\": " ++ nat_string(QuotientPruned) ++ ",\n" ++
            "  \"source_included_pruned_count\": " ++ nat_string(SourcePruned) ++ ",\n" ++
            "  \"novel_basis_count\": " ++ nat_string(list.length(Terms)) ++ ",\n" ++
            "  \"candidates\": [\n",
            !IO),
        term_names(Terms, Stream, !IO),
        io.write_string(Stream,
            "  ],\n" ++
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
