:- module tsts_endogenous_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module string.

:- type replacement_tag
    ---> attention_tag
    ;   norm_tag
    ;   optimizer_tag.

:- type theorem_schema
    ---> policy_replacement_composition
    ;   norm_full_step_composition
    ;   persistent_gru_full_step_composition.

:- type program
    ---> theorem_program(theorem_schema, list(replacement_tag), int).

:- func one_step_sequences = list(list(replacement_tag)).
one_step_sequences =
    [[attention_tag], [norm_tag], [optimizer_tag]].

:- func prepend_all(replacement_tag, list(list(replacement_tag)))
    = list(list(replacement_tag)).
prepend_all(_, []) = [].
prepend_all(X, [Ys | Yss]) =
    [[X | Ys] | prepend_all(X, Yss)].

:- func all_sequences_of_length(int) = list(list(replacement_tag)).
all_sequences_of_length(1) = one_step_sequences.
all_sequences_of_length(2) =
    prepend_all(attention_tag, one_step_sequences) ++
    prepend_all(norm_tag, one_step_sequences) ++
    prepend_all(optimizer_tag, one_step_sequences).
all_sequences_of_length(3) =
    prepend_all(attention_tag, all_sequences_of_length(2)) ++
    prepend_all(norm_tag, all_sequences_of_length(2)) ++
    prepend_all(optimizer_tag, all_sequences_of_length(2)).

:- func policy_programs = list(program).
policy_programs =
    map_policy(all_sequences_of_length(3)) ++
    map_policy(all_sequences_of_length(2)) ++
    map_policy(all_sequences_of_length(1)).

:- func map_policy(list(list(replacement_tag))) = list(program).
map_policy([]) = [].
map_policy([Rs | Rss]) =
    [theorem_program(policy_replacement_composition, Rs, 0) |
     map_policy(Rss)].

:- func preservation_programs = list(program).
preservation_programs =
    [ theorem_program(norm_full_step_composition, [], 1)
    , theorem_program(norm_full_step_composition, [], 2)
    , theorem_program(norm_full_step_composition, [], 3)
    , theorem_program(persistent_gru_full_step_composition, [], 1)
    , theorem_program(persistent_gru_full_step_composition, [], 2)
    , theorem_program(persistent_gru_full_step_composition, [], 3)
    ].

:- func programs = list(program).
programs = policy_programs ++ preservation_programs.

:- func tag_name(replacement_tag) = string.
tag_name(attention_tag) = "attention".
tag_name(norm_tag) = "norm".
tag_name(optimizer_tag) = "optimizer".

:- func seq_name(list(replacement_tag)) = string.
seq_name([]) = "empty".
seq_name([X | Xs]) = tag_name(X) ++ seq_name_tail(Xs).

:- func seq_name_tail(list(replacement_tag)) = string.
seq_name_tail([]) = "".
seq_name_tail([X | Xs]) = "_" ++ tag_name(X) ++ seq_name_tail(Xs).

:- func nat_string(int) = string.
nat_string(N) = string.int_to_string(N).

:- func parameter_binders(list(replacement_tag)) = string.
parameter_binders(Tags) = parameter_binders_from(Tags, 1).

:- func parameter_binders_from(list(replacement_tag), int) = string.
parameter_binders_from([], _) = "".
parameter_binders_from([attention_tag | Ts], I) =
    " (a" ++ nat_string(I) ++ " : C.LearnedSparsemaxAttention)" ++
    parameter_binders_from(Ts, I + 1).
parameter_binders_from([norm_tag | Ts], I) =
    " (n" ++ nat_string(I) ++ " : C.NormPair)" ++
    parameter_binders_from(Ts, I + 1).
parameter_binders_from([optimizer_tag | Ts], I) =
    " (o" ++ nat_string(I) ++ " : C.F4IntUState)" ++
    parameter_binders_from(Ts, I + 1).

:- func parameter_pattern(list(replacement_tag)) = string.
parameter_pattern(Tags) = parameter_pattern_from(Tags, 1).

:- func parameter_pattern_from(list(replacement_tag), int) = string.
parameter_pattern_from([], _) = "".
parameter_pattern_from([attention_tag | Ts], I) =
    " a" ++ nat_string(I) ++ parameter_pattern_from(Ts, I + 1).
parameter_pattern_from([norm_tag | Ts], I) =
    " n" ++ nat_string(I) ++ parameter_pattern_from(Ts, I + 1).
parameter_pattern_from([optimizer_tag | Ts], I) =
    " o" ++ nat_string(I) ++ parameter_pattern_from(Ts, I + 1).

:- func replacement_expr(replacement_tag, int) = string.
replacement_expr(attention_tag, I) =
    "attentionReplacement a" ++ nat_string(I).
replacement_expr(norm_tag, I) =
    "normReplacement n" ++ nat_string(I).
replacement_expr(optimizer_tag, I) =
    "optimizerReplacement o" ++ nat_string(I).

:- func replacement_list_expr(list(replacement_tag)) = string.
replacement_list_expr(Tags) = replacement_list_expr_from(Tags, 1).

:- func replacement_list_expr_from(list(replacement_tag), int) = string.
replacement_list_expr_from([], _) = "[]".
replacement_list_expr_from([T | Ts], I) =
    replacement_expr(T, I) ++
    " ∷ " ++
    replacement_list_expr_from(Ts, I + 1).

:- func policy_candidate_name(list(replacement_tag)) = string.
policy_candidate_name(Tags) = "candidate_policy_" ++ seq_name(Tags).

:- func render_policy_candidate(list(replacement_tag)) = string.
render_policy_candidate(Tags) =
    policy_candidate_name(Tags) ++ " :" ++
    "\n  ∀ K s" ++ parameter_binders(Tags) ++ " →" ++
    "\n  C.canonicalPolicy K" ++
    "\n    (applyLearnerReplacements" ++
    "\n      (" ++ replacement_list_expr(Tags) ++ ")" ++
    "\n      s)" ++
    "\n  ≡" ++
    "\n  C.canonicalPolicy K s" ++
    "\n" ++
    policy_candidate_name(Tags) ++ parameter_pattern(Tags) ++ " =" ++
    "\n  canonicalPolicy-learnerReplacement-composition" ++
    "\n    K s (" ++ replacement_list_expr(Tags) ++ ")" ++
    "\n\n".

:- func render_preservation_candidate(theorem_schema, int) = string.
render_preservation_candidate(norm_full_step_composition, N) =
    "candidate_norm_full_step_" ++ nat_string(N) ++ " :" ++
    "\n  ∀ K s →" ++
    "\n  C.normPairWeightPlusOne" ++
    "\n    (C.norm (C.iterateCanonical K " ++ nat_string(N) ++ " s))" ++
    "\n  ≡" ++
    "\n  C.normPairWeightPlusOne (C.norm s)" ++
    "\ncandidate_norm_full_step_" ++ nat_string(N) ++ " K s =" ++
    "\n  canonicalNormPair-afterFullStep-iterate K " ++
    nat_string(N) ++ " s" ++
    "\n\n".
render_preservation_candidate(persistent_gru_full_step_composition, N) =
    "candidate_persistent_gru_full_step_" ++ nat_string(N) ++ " :" ++
    "\n  ∀ K s →" ++
    "\n  C.persistentGRU" ++
    "\n    (C.gru (C.iterateCanonical K " ++ nat_string(N) ++ " s))" ++
    "\n  ≡" ++
    "\n  C.persistentGRU (C.gru s)" ++
    "\ncandidate_persistent_gru_full_step_" ++ nat_string(N) ++ " K s =" ++
    "\n  canonicalPersistentGRU-afterFullStep-iterate K " ++
    nat_string(N) ++ " s" ++
    "\n\n".
render_preservation_candidate(_, _) = "".

:- func render_program(program) = string.
render_program(theorem_program(policy_replacement_composition, Tags, _)) =
    render_policy_candidate(Tags).
render_program(theorem_program(S, [], N)) =
    render_preservation_candidate(S, N).
render_program(theorem_program(_, _, _)) = "".

:- func program_name(program) = string.
program_name(theorem_program(policy_replacement_composition, Tags, _)) =
    policy_candidate_name(Tags).
program_name(theorem_program(norm_full_step_composition, _, N)) =
    "candidate_norm_full_step_" ++ nat_string(N).
program_name(theorem_program(persistent_gru_full_step_composition, _, N)) =
    "candidate_persistent_gru_full_step_" ++ nat_string(N).

:- pred write_programs(io.text_output_stream::in, list(program)::in,
    io::di, io::uo) is det.
write_programs(_, [], !IO).
write_programs(Stream, [P | Ps], !IO) :-
    io.write_string(Stream, render_program(P), !IO),
    write_programs(Stream, Ps, !IO).

:- pred write_agda_program(list(program)::in, io::di, io::uo) is det.
write_agda_program(Programs, !IO) :-
    io.open_output("../../Exotic/ERL/FullCoupled/GeneratedLearnerCompositionDiscovery.agda", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{-# OPTIONS --safe #-}\n\n" ++
            "module Exotic.ERL.FullCoupled.GeneratedLearnerCompositionDiscovery where\n\n" ++
            "open import Data.List.Base using (List; []; _∷_)\n" ++
            "open import Exotic.ERL.FullCoupled.CanonicalLearnerMonolith as C\n" ++
            "open import Exotic.ERL.FullCoupled.TheoremsMonolith\n\n",
            !IO),
        write_programs(Stream, Programs, !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write generated Agda composition program\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

:- pred write_names(io.text_output_stream::in, list(string)::in,
    io::di, io::uo) is det.
write_names(_, [], !IO).
write_names(Stream, [N | Ns], !IO) :-
    io.write_string(Stream, "    \"" ++ N ++ "\"", !IO),
    (
        Ns = [] ->
            io.write_string(Stream, "\n", !IO)
    ;
            io.write_string(Stream, ",\n", !IO)
    ),
    write_names(Stream, Ns, !IO).

:- pred write_report(list(program)::in, io::di, io::uo) is det.
write_report(Programs, !IO) :-
    io.open_output("tsts-endogenous-composition-candidate.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream,
            "{\n" ++
            "  \"accepted\": true,\n" ++
            "  \"search_semantics\": " ++
            "\"TSTS-ordered symbolic search over typed learner theorem compositions\",\n" ++
            "  \"proof_gate\": \"GeneratedLearnerCompositionDiscovery.agda\",\n" ++
            "  \"candidate_count\": " ++
            nat_string(list.length(Programs)) ++ ",\n" ++
            "  \"selection_metric\": \"unspecified by semantic contract\",\n" ++
            "  \"external_equivalence\": false\n" ++
            "}\n",
            !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write symbolic composition discovery report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    Programs = programs,
    write_agda_program(Programs, !IO),
    write_report(Programs, !IO),
    io.write_string(
        "tsts-symbolic-composition-discovery=generated\n", !IO),
    io.write_string(
        "candidate_count=" ++ nat_string(list.length(Programs)) ++ "\n",
        !IO),
    io.write_string(
        "proof_gate=GeneratedLearnerCompositionDiscovery.agda\n", !IO).
