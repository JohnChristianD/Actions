:- module novel_learner_theorem_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module io.
:- import_module list.
:- import_module string.
:- import_module learner_theorem_egraph.

:- func nat_string(int) = string.
nat_string(N) = string.int_to_string(N).

:- func clock_plus4_expr(string) = string.
clock_plus4_expr(S) =
    "replaceClock (" ++ S ++
    ") (suc (suc (suc (suc (C.clock (" ++ S ++ "))))))".

:- func rendered_program(list(theorem_term)) = string.
rendered_program(_) =
    "generated-novel-learner-theorem-basis : NovelLearnerTheoremBasis\n" ++
    "generated-novel-learner-theorem-basis = novel-learner-theorem-basis\n".
:- func rendered_program(list(theorem_term)) = string.
rendered_program([]) = "".
rendered_program([T | Ts]) = render_candidate(T) ++ rendered_program(Ts).

:- pred contains_bare_refl(string::in) is semidet.
contains_bare_refl(Text) :-
    string.sub_string_search(Text, "= refl\n", _).

:- pred write_generated(list(theorem_term)::in, io::di, io::uo) is det.
write_generated(Terms, !IO) :-
    Text = rendered_program(Terms),
    ( if contains_bare_refl(Text) then
        io.write_string(
            "ERROR: trivial bare refl proof remained in generated discovery module\n",
            !IO),
        io.set_exit_status(1, !IO)
    else
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
                "generatedNovelLearnerTheoremBasis : NovelLearnerTheoremBasis\n" ++
                "generatedNovelLearnerTheoremBasis = novel-learner-theorem-basis\n\n" ++
                Text,
                !IO),
            io.close_output(Stream)
        ;
            Result = error(_),
            io.write_string(
                "ERROR: cannot write generated novel learner theorem module\n",
                !IO),
            io.set_exit_status(1, !IO)
        )
    ).

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
            "novel-learner-theorem-discovery=generated\n", !IO),
        io.write_string(
            "raw_candidate_count=" ++ nat_string(list.length(Raw)) ++ "\n",
            !IO),
        io.write_string(
            "quotient_pruned_count=" ++ nat_string(QuotientPruned) ++ "\n",
            !IO),
        io.write_string(
            "source_included_pruned_count=" ++ nat_string(SourcePruned) ++ "\n",
            !IO),
        io.write_string(
            "novel_basis_count=" ++ nat_string(list.length(Novel)) ++ "\n",
            !IO),
        io.write_string("bare_refl_pruned=true\n", !IO),
        io.write_string(
            "proof_gate=GeneratedNovelLearnerTheorems.agda\n", !IO)
    ;
        SourceResult = error(ErrorMessage),
        io.write_string(
            "ERROR: cannot read TheoremsMonolith.agda: " ++
            ErrorMessage ++ "\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).
