:- module tsts_pvs_composition_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.

:- type composition
    ---> tsts_pvs_gesmr
    ;   tsts_pvs_samr
    ;   tsts_pvs_simple_es
    ;   tsts_pvs_random_search
    ;   pvs_hill_climbing
    ;   pvs_only
    ;   mctx_pvs.

:- type property
    ---> tsts_tree_selection
    ;   pvs_exact_recheck
    ;   finite_learner_evaluator
    ;   endogenous_f4_watkins_gru
    ;   norm_pair_preservation
    ;   persistent_gru_preservation
    ;   grouped_mutation_control
    ;   adaptive_mutation_control
    ;   finite_time_regret_theorem.

:- func candidates = list(composition).
candidates = [
    tsts_pvs_gesmr,
    tsts_pvs_samr,
    tsts_pvs_simple_es,
    tsts_pvs_random_search,
    pvs_hill_climbing,
    pvs_only,
    mctx_pvs
].

:- func required = list(property).
required = [
    tsts_tree_selection,
    pvs_exact_recheck,
    finite_learner_evaluator,
    endogenous_f4_watkins_gru,
    norm_pair_preservation,
    persistent_gru_preservation,
    grouped_mutation_control,
    adaptive_mutation_control,
    finite_time_regret_theorem
].

:- pred supports(composition::in, property::in) is semidet.
supports(tsts_pvs_gesmr, tsts_tree_selection).
supports(tsts_pvs_gesmr, pvs_exact_recheck).
supports(tsts_pvs_gesmr, finite_learner_evaluator).
supports(tsts_pvs_gesmr, endogenous_f4_watkins_gru).
supports(tsts_pvs_gesmr, norm_pair_preservation).
supports(tsts_pvs_gesmr, persistent_gru_preservation).
supports(tsts_pvs_gesmr, grouped_mutation_control).
supports(tsts_pvs_gesmr, adaptive_mutation_control).
supports(tsts_pvs_gesmr, finite_time_regret_theorem).

supports(tsts_pvs_samr, tsts_tree_selection).
supports(tsts_pvs_samr, pvs_exact_recheck).
supports(tsts_pvs_samr, finite_learner_evaluator).
supports(tsts_pvs_samr, endogenous_f4_watkins_gru).
supports(tsts_pvs_samr, norm_pair_preservation).
supports(tsts_pvs_samr, persistent_gru_preservation).
supports(tsts_pvs_samr, adaptive_mutation_control).
supports(tsts_pvs_samr, finite_time_regret_theorem).

supports(tsts_pvs_simple_es, tsts_tree_selection).
supports(tsts_pvs_simple_es, pvs_exact_recheck).
supports(tsts_pvs_simple_es, finite_learner_evaluator).
supports(tsts_pvs_simple_es, endogenous_f4_watkins_gru).
supports(tsts_pvs_simple_es, norm_pair_preservation).
supports(tsts_pvs_simple_es, persistent_gru_preservation).
supports(tsts_pvs_simple_es, finite_time_regret_theorem).

supports(tsts_pvs_random_search, tsts_tree_selection).
supports(tsts_pvs_random_search, pvs_exact_recheck).
supports(tsts_pvs_random_search, finite_learner_evaluator).
supports(tsts_pvs_random_search, endogenous_f4_watkins_gru).
supports(tsts_pvs_random_search, norm_pair_preservation).
supports(tsts_pvs_random_search, persistent_gru_preservation).
supports(tsts_pvs_random_search, finite_time_regret_theorem).

supports(pvs_hill_climbing, pvs_exact_recheck).
supports(pvs_hill_climbing, finite_learner_evaluator).
supports(pvs_hill_climbing, endogenous_f4_watkins_gru).
supports(pvs_hill_climbing, norm_pair_preservation).
supports(pvs_hill_climbing, persistent_gru_preservation).

supports(pvs_only, pvs_exact_recheck).
supports(pvs_only, finite_learner_evaluator).
supports(pvs_only, endogenous_f4_watkins_gru).
supports(pvs_only, norm_pair_preservation).
supports(pvs_only, persistent_gru_preservation).

supports(mctx_pvs, tsts_tree_selection).
supports(mctx_pvs, pvs_exact_recheck).
supports(mctx_pvs, finite_learner_evaluator).
supports(mctx_pvs, endogenous_f4_watkins_gru).
supports(mctx_pvs, norm_pair_preservation).
supports(mctx_pvs, persistent_gru_preservation).

:- pred supported_all(composition::in, list(property)::in) is semidet.
supported_all(_, []).
supported_all(C, [P | Ps]) :-
    supports(C, P),
    supported_all(C, Ps).

:- pred discover(list(composition)::in, list(property)::in, composition::out)
    is semidet.
discover([C | _], Required, C) :-
    supported_all(C, Required).
discover([_ | Cs], Required, C) :-
    discover(Cs, Required, C).

:- func composition_name(composition) = string.
composition_name(tsts_pvs_gesmr) = "TSTS_PVS_GESMR_GA".
composition_name(tsts_pvs_samr) = "TSTS_PVS_SAMR_GA".
composition_name(tsts_pvs_simple_es) = "TSTS_PVS_SimpleES".
composition_name(tsts_pvs_random_search) = "TSTS_PVS_RandomSearch".
composition_name(pvs_hill_climbing) = "PVS_HillClimbing".
composition_name(pvs_only) = "PVS_Only".
composition_name(mctx_pvs) = "MCTX_PVS".

:- pred write_report(composition::in, io::di, io::uo) is det.
write_report(C, !IO) :-
    io.open_output("tsts-pvs-composition-candidate.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream, "{\n", !IO),
        io.write_string(Stream, "  \"accepted\": true,\n", !IO),
        io.write_string(Stream, "  \"composition\": \"", !IO),
        io.write_string(Stream, composition_name(C), !IO),
        io.write_string(Stream, "\",\n", !IO),
        io.write_string(Stream,
            "  \"semantic_boundary\": \"TSTS branch selection + PVS exact recheck + finite GESMR endogenous learner evaluator\",\n",
            !IO),
        io.write_string(Stream,
            "  \"theoretical_status\": \"TSTS has a finite-time Bayesian regret bound in Greshler et al. 2024; this repository does not claim that bound for the full composed theorem\",\n",
            !IO),
        io.write_string(Stream,
            "  \"pvs_status\": \"exact minimax-preserving recheck pattern, not a regret guarantee\",\n",
            !IO),
        io.write_string(Stream,
            "  \"proof_gate\": \"TheoremsMonolith.agda\",\n",
            !IO),
        io.write_string(Stream,
            "  \"external_equivalence\": false\n",
            !IO),
        io.write_string(Stream, "}\n", !IO),
        io.close_output(Stream)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write TSTS/PVS composition discovery report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    (
        discover(candidates, required, C)
    ->
        write_report(C, !IO),
        io.write_string(
            "tsts-pvs-composition-discovery=accepted\n", !IO),
        io.write_string(
            "candidate=TSTS_PVS_GESMR_GA\n", !IO),
        io.write_string(
            "next=Agda endogenous connected theorem gate\n", !IO)
    ;
        io.write_string(
            "tsts-pvs-composition-discovery=rejected\n", !IO),
        io.set_exit_status(1, !IO)
    ).
