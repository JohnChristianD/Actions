:- module formal_openes_composition_discovery.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.

:- type variation
    ---> open_es
    ;   gradientless_descent
    ;   simulated_annealing
    ;   hill_climbing
    ;   random_search
    ;   particle_swarm
    ;   differential_evolution.

:- type property
    ---> two_sided_probe
    ;   antithetic_estimator
    ;   f4_l2_tell
    ;   canonical_learner_evaluator
    ;   norm_pair_preservation
    ;   persistent_gru_preservation.

:- func candidates = list(variation).
candidates = [
    open_es,
    gradientless_descent,
    simulated_annealing,
    hill_climbing,
    random_search,
    particle_swarm,
    differential_evolution
].

:- func required = list(property).
required = [
    two_sided_probe,
    antithetic_estimator,
    f4_l2_tell,
    canonical_learner_evaluator,
    norm_pair_preservation,
    persistent_gru_preservation
].

:- pred supports(variation::in, property::in) is semidet.
supports(open_es, two_sided_probe).
supports(open_es, antithetic_estimator).
supports(open_es, f4_l2_tell).
supports(open_es, canonical_learner_evaluator).
supports(open_es, norm_pair_preservation).
supports(open_es, persistent_gru_preservation).

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
variation_name(open_es) = "Open_ES".
variation_name(gradientless_descent) = "GradientlessDescent".
variation_name(simulated_annealing) = "SimAnneal".
variation_name(hill_climbing) = "HillClimbing".
variation_name(random_search) = "RandomSearch".
variation_name(particle_swarm) = "PSO".
variation_name(differential_evolution) = "DifferentialEvolution".

:- pred write_report(variation::in, io::di, io::uo) is det.
write_report(V, !IO) :-
    io.open_output("openes-composition-candidate.json", Result, !IO),
    (
        Result = ok(Stream),
        io.write_string(Stream, "{\n", !IO),
        io.write_string(Stream, "  \"accepted\": true,\n", !IO),
        io.write_string(Stream, "  \"variation\": \"", !IO),
        io.write_string(Stream, variation_name(V), !IO),
        io.write_string(Stream, "\",\n", !IO),
        io.write_string(Stream,
            "  \"semantic_boundary\": \"finite OpenAI-ES ask/evaluate/tell over F4/L2 with Agda learner evaluator\",\n",
            !IO),
        io.write_string(Stream,
            "  \"proof_gate\": \"TheoremsMonolith.agda\",\n",
            !IO),
        io.write_string(Stream,
            "  \"external_equivalence\": false\n",
            !IO),
        io.write_string(Stream, "}\n", !IO),
        io.close_output(Stream, !IO)
    ;
        Result = error(_),
        io.write_string(
            "ERROR: cannot write OpenES composition discovery report\n",
            !IO),
        io.set_exit_status(1, !IO)
    ).

main(!IO) :-
    (
        discover(candidates, required, V)
    ->
        write_report(V, !IO),
        io.write_string(
            "formal-openes-composition-discovery=accepted\n", !IO),
        io.write_string(
            "candidate=Open_ES\n", !IO),
        io.write_string(
            "next=Agda monolith proof gate\n", !IO)
    ;
        io.write_string(
            "formal-openes-composition-discovery=rejected\n", !IO),
        io.set_exit_status(1, !IO)
    ).
