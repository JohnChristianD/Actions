:- module formal_gesmr_composition_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.

:- type variation
    ---> gesmr_ga
    ;   mr15_ga
    ;   open_es
    ;   hill_climbing
    ;   mctx
    ;   particle_swarm
    ;   differential_evolution.

:- type property
    ---> population_elitism
    ;   adaptive_mutation_rate
    ;   grouped_mutation_rates
    ;   canonical_learner_evaluator
    ;   watkins_f4_l2_gru_tell
    ;   norm_pair_preservation
    ;   persistent_gru_preservation
    ;   tree_search.

:- func candidates = list(variation).
candidates = [
    gesmr_ga,
    mr15_ga,
    open_es,
    hill_climbing,
    mctx,
    particle_swarm,
    differential_evolution
].

:- func required = list(property).
required = [
    population_elitism,
    adaptive_mutation_rate,
    grouped_mutation_rates,
    canonical_learner_evaluator,
    watkins_f4_l2_gru_tell,
    norm_pair_preservation,
    persistent_gru_preservation
].

:- pred supports(variation::in, property::in) is semidet.
supports(gesmr_ga, population_elitism).
supports(gesmr_ga, adaptive_mutation_rate).
supports(gesmr_ga, grouped_mutation_rates).
supports(gesmr_ga, canonical_learner_evaluator).
supports(gesmr_ga, watkins_f4_l2_gru_tell).
supports(gesmr_ga, norm_pair_preservation).
supports(gesmr_ga, persistent_gru_preservation).
supports(mr15_ga, population_elitism).
supports(mr15_ga, adaptive_mutation_rate).
supports(mr15_ga, canonical_learner_evaluator).
supports(mr15_ga, watkins_f4_l2_gru_tell).
supports(mr15_ga, norm_pair_preservation).
supports(mr15_ga, persistent_gru_preservation).
supports(open_es, canonical_learner_evaluator).
supports(open_es, watkins_f4_l2_gru_tell).
supports(open_es, norm_pair_preservation).
supports(open_es, persistent_gru_preservation).
supports(hill_climbing, canonical_learner_evaluator).
supports(hill_climbing, watkins_f4_l2_gru_tell).
supports(hill_climbing, norm_pair_preservation).
supports(hill_climbing, persistent_gru_preservation).
supports(mctx, tree_search).
supports(mctx, canonical_learner_evaluator).
supports(particle_swarm, adaptive_mutation_rate).
supports(particle_swarm, canonical_learner_evaluator).
supports(differential_evolution, adaptive_mutation_rate).
supports(differential_evolution, canonical_learner_evaluator).

:- pred supported_all(variation::in, list(property)::in) is semidet.
supported_all(_, []).
supported_all(V, [P | Ps]) :-
    supports(V, P),
    supported_all(V, Ps).

:- pred discover(list(variation)::in, list(property)::in, variation::out)
    is semidet.
discover([V | _], Required, V) :-
    supported_all(V, Required).
discover([_ | Vs], Required, V) :-
    discover(Vs, Required, V).

:- func variation_name(variation) = string.
variation_name(gesmr_ga) = "GESMR_GA".
variation_name(mr15_ga) = "MR15_GA".
variation_name(open_es) = "Open_ES".
variation_name(hill_climbing) = "HillClimbing".
variation_name(mctx) = "MCTX".
variation_name(particle_swarm) = "PSO".
variation_name(differential_evolution) = "DifferentialEvolution".

:- pred write_report(variation::in, io::di, io::uo) is det.
write_report(V, !IO) :-
    io.open_output("gesmr-composition-candidate.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream, "{\n", !IO),
        io.write_string(Stream, "  \"accepted\": true,\n", !IO),
        io.write_string(Stream, "  \"variation\": \"", !IO),
        io.write_string(Stream, variation_name(V), !IO),
        io.write_string(Stream, "\",\n", !IO),
        io.write_string(Stream,
            "  \"semantic_boundary\": \"finite GESMR grouped-mutation control over Watkins/F4-L2/GRU learner probes\",\n",
            !IO),
        io.write_string(Stream,
            "  \"proof_gate\": \"TheoremsMonolith.agda\",\n", !IO),
        io.write_string(Stream,
            "  \"external_equivalence\": false\n", !IO),
        io.write_string(Stream, "}\n", !IO),
        io.close_output(Stream, !IO)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write GESMR composition discovery report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    (
        discover(candidates, required, V)
    ->
        write_report(V, !IO),
        io.write_string(
            "formal-gesmr-composition-discovery=accepted\n", !IO),
        io.write_string(
            "candidate=GESMR_GA\n", !IO),
        io.write_string(
            "next=Agda endogenous theorem gate\n", !IO)
    ;
        io.write_string(
            "formal-gesmr-composition-discovery=rejected\n", !IO),
        io.set_exit_status(1, !IO)
    ).
